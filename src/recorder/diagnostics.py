"""跑轴记录全动作诊断与跨版本 A/B 对比。不依赖 Qt, 兼容新旧两代 JSONL 记录。"""
import statistics

from .runs import HUD_HIDDEN, RunData, _num


def _is_f_break_event(event):
    if str(event.get('k', '')).lower() != 'f':
        return False
    if event.get('a') not in ('key', 'kd'):
        return False
    joined = ' '.join(str(event.get(k) or '') for k in ('src', 'src2', 'via')).lower()
    return 'f_break' in joined or 'combatcheck' in joined


def _analyze_switches(run):
    """统计切人(按 1/2/3 到 field 切过去)的次数、总耗时、平均耗时与最慢 Top3。"""
    events = sorted(
        (e for e in run.events if e.get('e') in ('in', 'field')),
        key=lambda e: e.get('t', 0),
    )
    switches = []
    pending = None
    cur_field = None
    for e in events:
        t = e['t']
        if e['e'] == 'in':
            if e.get('a') not in ('key', 'kd') or e.get('si'):
                continue
            key = str(e.get('k', ''))
            if key not in ('1', '2', '3', '4'):
                continue
            target = int(key) - 1
            if cur_field is not None and cur_field[0] and cur_field[1] == target:
                continue
            if pending is None or pending['to'] != target or t - pending['t0'] > 4.0:
                pending = {
                    't0': t,
                    'from': cur_field[1] if cur_field and cur_field[0] else run.owner_at(t),
                    'to': target,
                    'presses': 1,
                }
            else:
                pending['presses'] += 1
        else:
            state = (bool(e.get('team')), int(e.get('i', -1)))
            if pending and state[0] and state[1] == pending['to']:
                dur = t - pending['t0']
                if 0 <= dur <= 4.0:
                    switches.append({
                        't': pending['t0'],
                        't1': t,
                        'from': pending['from'],
                        'to': pending['to'],
                        'dur': dur,
                        'presses': pending['presses'],
                    })
                pending = None
            cur_field = state

    total_s = sum(s['dur'] for s in switches)
    avg_s = total_s / len(switches) if switches else 0.0
    slowest = sorted(switches, key=lambda s: s['dur'], reverse=True)[:3]
    return {
        'count': len(switches),
        'total_s': total_s,
        'avg_s': avg_s,
        'items': switches,
        'slowest': slowest,
    }


def _analyze_f_break(run, switches):
    """统计 CombatCheck.f_break / 自动 F 的按键次数、总跨度与切人期间白按 F。"""
    f_events = [e for e in run.events if e.get('e') == 'in' and _is_f_break_event(e)]
    if not f_events:
        return {'count': 0, 'total_s': 0.0, 'switch_count': 0, 'switch_s': 0.0}
    clusters = []
    cur = [f_events[0]['t'], f_events[0]['t'], 1]
    for e in f_events[1:]:
        t = e['t']
        if t - cur[1] <= 0.45:
            cur[1] = t
            cur[2] += 1
        else:
            clusters.append(cur)
            cur = [t, t, 1]
    clusters.append(cur)

    def _span_dur(t0, t1):
        return max(0.12, (t1 - t0) + 0.12)

    total_s = sum(_span_dur(a, b) for a, b, _ in clusters)
    sw_windows = [(s['t'] - 0.15, s['t1'] + 0.25) for s in switches['items']]
    sw_count = 0
    sw_s = 0.0
    for a, b, cnt in clusters:
        if any(a <= w1 and b >= w0 for w0, w1 in sw_windows):
            sw_count += cnt
            sw_s += _span_dur(a, b)
    return {
        'count': len(f_events),
        'total_s': total_s,
        'switch_count': sw_count,
        'switch_s': sw_s,
    }


def _analyze_swallowed_skills(run):
    """检测按 E/Q 后 0.6s 内冷却仍 <=0 且未进动画的疑似吞键(仅在有对应读屏或 hud 覆盖时)。"""
    cd_reads = [
        e for e in run.events
        if e.get('e') == 'read' and e.get('k') == 'cd' and e.get('name') in ('resonance', 'echo')
    ]
    huds = getattr(run, 'huds', [])
    suspects = []
    seen_buckets = set()
    for e in run.events:
        if e.get('e') != 'in' or e.get('a') not in ('key', 'kd') or e.get('si'):
            continue
        label = run.input_label(e)
        if label not in ('E', 'Q'):
            continue
        target_name = 'resonance' if label == 'E' else 'echo'
        t = e['t']
        # 同一段连按只算最后一个按下的确认窗口
        bucket = (label, round(t * 2) / 2)
        if bucket in seen_buckets:
            continue
        seen_buckets.add(bucket)
        later = [
            r for r in cd_reads
            if r['name'] == target_name and r['t'] >= t + 0.12 and r['t'] <= t + 0.55
        ]
        if later:
            max_v = max(float(r.get('hi', r.get('v', 0)) or 0) for r in later)
            if max_v <= 0:
                suspects.append({'t': t, 'key': label, 'slot': run.owner_at(t), 'why': f'cd<={max_v:.2f}'})
            continue
        if huds:
            idx = 0 if label == 'E' else 2
            before = [h for h in huds if t - 0.35 <= h['t'] <= t and run.is_hud_visible_at(h['t'])]
            after = [h for h in huds if t + 0.15 <= h['t'] <= t + 0.65 and run.is_hud_visible_at(h['t'])]
            if before and after and before[-1].get('sk') and after[0].get('sk'):
                v0 = before[-1]['sk'][idx]
                v1 = min(h['sk'][idx] for h in after)
                # 技能栏图标原本高亮且按键后完全没有暗下来(通常进 CD 会掉落显著比例)
                if v0 >= 0.08 and v1 >= v0 * 0.90:
                    suspects.append({'t': t, 'key': label, 'slot': run.owner_at(t), 'why': f'sk{idx}={v0:.2f}->{v1:.2f}'})
    return suspects


def _analyze_unconsumed_holds(run):
    """检测长按左键 (>=0.35s) 结束时回路仍满的疑似吞重击。"""
    forte_reads = [
        e for e in run.events
        if e.get('e') == 'read' and e.get('name') in ('mouse_forte', 'forte_full')
    ]
    huds = getattr(run, 'huds', [])
    suspects = []
    for hold in run.holds:
        if hold.label != '按住A':
            continue
        dur = hold.t1 - hold.t0
        if dur < 0.35:
            continue
        t0, t1 = hold.t0, hold.t1
        # 先看读屏事件
        after_reads = [r for r in forte_reads if t1 - 0.10 <= r['t'] <= t1 + 0.25]
        still_full = False
        why = ''
        for r in after_reads:
            if r.get('name') == 'mouse_forte' and r.get('ok'):
                still_full = True
                why = 'mouse_forte仍亮'
                break
            if r.get('name') == 'forte_full' and float(r.get('v') or 0) > 0.08:
                still_full = True
                why = f"forte_full={_num(r.get('v'))}"
                break
        if not still_full and huds:
            owner0 = run.owner_at(t0)
            near_start = [
                h for h in huds
                if t0 - 0.2 <= h['t'] <= t0 + 0.35 and run.is_hud_visible_at(h['t'])
            ]
            after_hud = [
                h for h in huds
                if t1 <= h['t'] <= t1 + 0.55
                and run.is_hud_visible_at(h['t'])
                and (owner0 is None or run.owner_at(h['t']) in (None, owner0))
            ]
            if near_start and after_hud:
                f_start = max(float(h.get('f', 0) or 0) for h in near_start)
                f_end = min(float(h.get('f', 0) or 0) for h in after_hud)
                if f_start >= 0.20 and f_end >= 0.20:
                    still_full = True
                    why = f'hud.f {f_start:.2f}->{f_end:.2f}'
        if still_full:
            suspects.append({
                't': t0,
                'dur': dur,
                'slot': run.owner_at(t0),
                'why': why,
            })
    return suspects


def _analyze_boss_hp(run):
    all_huds = getattr(run, 'huds', [])
    pts = [
        (e['t'], float(e['hp']))
        for e in all_huds
        if e.get('hp') is not None and run.is_hud_visible_at(e['t'])
    ]
    if len(pts) < 2:
        return None
    if len(all_huds) >= 20 and len(pts) < 5:
        return None
    if len(all_huds) >= 40 and len(pts) / len(all_huds) < 0.10:
        return None
    cleaned = []
    for i, pt in enumerate(pts):
        if 0 < i < len(pts) - 1:
            prev_hp = cleaned[-1][1] if cleaned else pts[i - 1][1]
            cur_hp = pt[1]
            next_hp = pts[i + 1][1]
            # 过滤大招淡入淡出/技能特效短暂遮挡造成的单点 V 型骤降毛刺
            if prev_hp - cur_hp >= 0.15 and next_hp - cur_hp >= 0.15 and next_hp <= prev_hp + 0.05:
                continue
        cleaned.append(pt)
    if len(cleaned) < 2:
        return None
    total_drop = 0.0
    prev_t, prev_hp = cleaned[0]
    for t, hp in cleaned[1:]:
        diff = prev_hp - hp
        if diff > 0:
            total_drop += diff
        # 若血条跳回 +0.25 以上视作换怪/多波次重置, 不扣除但重设基准
        prev_t, prev_hp = t, hp
    span = max(0.1, cleaned[-1][0] - cleaned[0][0])
    return {
        'samples': len(cleaned),
        'start_hp': cleaned[0][1],
        'end_hp': cleaned[-1][1],
        'total_drop': total_drop,
        'drop_per_s': (total_drop * 100.0) / span,
    }


def analyze_run(run):
    """对单局 RunData 执行全动作与吞键诊断, 返回结构化字典。"""
    switches = _analyze_switches(run)
    f_break = _analyze_f_break(run, switches)
    swallowed = _analyze_swallowed_skills(run)
    unconsumed = _analyze_unconsumed_holds(run)
    boss_hp = _analyze_boss_hp(run)
    warns = sum(1 for e in run.logs if (e.get('l') or 0) == 30)
    errors = sum(1 for e in run.logs if (e.get('l') or 0) >= 40)
    return {
        'switches': switches,
        'f_break': f_break,
        'swallowed_skills': swallowed,
        'unconsumed_holds': unconsumed,
        'boss_hp': boss_hp,
        'warns': warns,
        'errors': errors,
    }


def format_diagnostics(run, diag):
    """把 analyze_run 结果格式化成几行简洁的中文诊断输出。"""
    lines = []
    sw = diag['switches']
    if sw['count']:
        top = ', '.join(
            f"{s['t']:.1f}s {run.char_name(s['from'])}->{run.char_name(s['to'])} {s['dur']:.2f}s(x{s['presses']})"
            for s in sw['slowest']
        )
        lines.append(
            f"切人耗时: {sw['count']} 次共 {sw['total_s']:.2f}s(均 {sw['avg_s']:.2f}s); 最慢: {top}"
        )
    fb = diag['f_break']
    if fb['count']:
        extra = f", 其中切人期占 {fb['switch_s']:.2f}s({fb['switch_count']} 下)" if fb['switch_count'] else ''
        lines.append(f"自动F(f_break): {fb['count']} 下约 {fb['total_s']:.2f}s{extra}")
    if diag['swallowed_skills']:
        items = ', '.join(
            f"{s['t']:.2f}s {run.char_name(s['slot'])}.{s['key']}({s['why']})"
            for s in diag['swallowed_skills'][:8]
        )
        lines.append(f"疑似吞技能({len(diag['swallowed_skills'])}): {items}")
    if diag['unconsumed_holds']:
        items = ', '.join(
            f"{u['t']:.2f}s {run.char_name(u['slot'])} 按住{u['dur']:.2f}s({u['why']})"
            for u in diag['unconsumed_holds'][:6]
        )
        lines.append(f"疑似重击未耗条({len(diag['unconsumed_holds'])}): {items}")
    hp = diag['boss_hp']
    if hp:
        lines.append(
            f"Boss血量遥测({hp['samples']}点): 初始 {hp['start_hp']*100:.1f}% -> 结束 {hp['end_hp']*100:.1f}%, "
            f"累计掉血 {hp['total_drop']*100:.1f}% ({hp['drop_per_s']:.2f}%/s)"
        )
    return lines


def compare_runs(run_a, run_b, lap_slot_a=None, lap_slot_b=None):
    """生成两局记录的 A/B 指标对比文本行列表。"""
    def _pack(run, slot):
        slot = slot if slot is not None else run.default_lap_slot()
        laps = run.laps(slot) if slot is not None else []
        durs = [d for _, d in laps]
        mean_lap = sum(durs) / len(durs) if durs else None
        med_lap = statistics.median(durs) if durs else None
        ver = run.header.get('team_ver') or '-'
        name = f"{run.header.get('team_dir') or 'unknown'} v{ver}"
        return {
            'name': name,
            'laps': len(laps),
            'mean_lap': mean_lap,
            'med_lap': med_lap,
            'diag': analyze_run(run),
            'stats': run.char_stats(),
        }

    a = _pack(run_a, lap_slot_a)
    b = _pack(run_b, lap_slot_b)
    da, db = a['diag'], b['diag']
    lines = [
        f"对比 A: {a['name']} ({run_a.duration:.2f}s, {run_a.reason})",
        f"对比 B: {b['name']} ({run_b.duration:.2f}s, {run_b.reason})",
        '',
        f"{'指标':<18} {'A':>14} {'B':>14} {'变化(B-A)':>14}",
        '-' * 64,
        f"{'总时长(s)':<18} {run_a.duration:>14.2f} {run_b.duration:>14.2f} {run_b.duration - run_a.duration:>+14.2f}",
        f"{'完整圈数':<18} {a['laps']:>14d} {b['laps']:>14d} {b['laps'] - a['laps']:>+14d}",
    ]
    if a['mean_lap'] is not None and b['mean_lap'] is not None:
        lines.append(
            f"{'平均圈速(s)':<18} {a['mean_lap']:>14.2f} {b['mean_lap']:>14.2f} "
            f"{b['mean_lap'] - a['mean_lap']:>+14.2f}"
        )
        lines.append(
            f"{'中位圈速(s)':<18} {a['med_lap']:>14.2f} {b['med_lap']:>14.2f} "
            f"{b['med_lap'] - a['med_lap']:>+14.2f}"
        )
    lines.extend([
        f"{'切人总耗时(s)':<17} {da['switches']['total_s']:>14.2f} {db['switches']['total_s']:>14.2f} "
        f"{db['switches']['total_s'] - da['switches']['total_s']:>+14.2f}",
        f"{'切人次数':<18} {da['switches']['count']:>14d} {db['switches']['count']:>14d} "
        f"{db['switches']['count'] - da['switches']['count']:>+14d}",
        f"{'自动F耗时(s)':<17} {da['f_break']['total_s']:>14.2f} {db['f_break']['total_s']:>14.2f} "
        f"{db['f_break']['total_s'] - da['f_break']['total_s']:>+14.2f}",
        f"{'疑吞重击(次)':<17} {len(da['unconsumed_holds']):>14d} {len(db['unconsumed_holds']):>14d} "
        f"{len(db['unconsumed_holds']) - len(da['unconsumed_holds']):>+14d}",
        f"{'WARN/ERROR':<18} {da['warns']+da['errors']:>14d} {db['warns']+db['errors']:>14d} "
        f"{(db['warns']+db['errors']) - (da['warns']+da['errors']):>+14d}",
    ])
    if da['boss_hp'] and db['boss_hp']:
        ra, rb = da['boss_hp']['drop_per_s'], db['boss_hp']['drop_per_s']
        lines.append(f"{'掉血速率(%/s)':<16} {ra:>14.2f} {rb:>14.2f} {rb - ra:>+14.2f}")

    # 分角色在场占比与上场次数
    names_a = {s['name']: s for s in a['stats'].values()}
    names_b = {s['name']: s for s in b['stats'].values()}
    all_names = list(dict.fromkeys([*names_a, *names_b]))
    if all_names:
        lines.append('\n各角色上场分布(总秒数 / 上场次数):')
        for cname in all_names:
            sa = names_a.get(cname) or {'field': 0.0, 'entries': 0}
            sb = names_b.get(cname) or {'field': 0.0, 'entries': 0}
            va = f"{sa['field']:.1f}s/{sa['entries']}次"
            vb = f"{sb['field']:.1f}s/{sb['entries']}次"
            lines.append(f"  {cname:<14} A={va:<14} B={vb:<14} (净时长 {sb['field'] - sa['field']:+.1f}s)")
    return lines
