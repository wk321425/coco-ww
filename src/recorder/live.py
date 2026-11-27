"""详细面板用: 边追读正在写的那局记录, 边算在场时间线、圈速和延迟。不依赖 Qt, 测试能直接跑。

记录器的写盘线程每条事件写一行 JSON (逐行 flush), 这里每次只读文件新增的部分。
读屏事件 (read) 占了文件的大头, 面板用不上, 按行首直接跳过不解析。
在场段、分圈这些算法用跑轴复盘页同一套 (runs.RunData), 两边对得上。
"""
import json
import os

from .latency import analyse, median_ms
from .recorder import default_out_dir, list_run_files
from .runs import HUD_HIDDEN, RunData

KEEP = frozenset(('field', 'perf', 'in', 'log', 'mark'))
SKIP_PREFIXES = (b'{"e":"read"', b'{"e":"hud"')
READ_CHUNK = 4 << 20


class RunTail:
    """追读一局记录文件。poll() 读新增部分, data() 给出这局目前为止的 RunData。"""

    def __init__(self, path):
        self.path = path
        self.offset = 0
        self.header = {}
        self.end = None
        self.events = []
        self._rest = b''
        self._data = None

    def _reset(self):
        self.offset = 0
        self.header = {}
        self.end = None
        self.events = []
        self._rest = b''
        self._data = None

    def poll(self):
        """读文件新写进来的部分; 有新事件返回 True。"""
        try:
            size = os.path.getsize(self.path)
            if size < self.offset:
                self._reset()  # 文件被换掉或截短了, 从头再读
            if size == self.offset:
                return False
            with open(self.path, 'rb') as f:
                f.seek(self.offset)
                chunk = f.read(READ_CHUNK)
        except OSError:
            return False
        self.offset += len(chunk)
        lines = (self._rest + chunk).split(b'\n')
        self._rest = lines.pop()  # 最后一段可能还没写完, 留到下次
        changed = False
        for line in lines:
            line = line.strip()
            if not line or line.startswith(SKIP_PREFIXES):
                continue
            try:
                event = json.loads(line)
            except ValueError:
                continue
            kind = event.get('e') if isinstance(event, dict) else None
            if kind == 'start':
                self.header = event
            elif kind == 'end':
                self.end = event
            elif kind in KEEP:
                self.events.append(event)
            else:
                continue
            changed = True
        if changed:
            self._data = None
        return changed

    def data(self):
        if self._data is None:
            self._data = RunData(self.path, parsed=(self.header, self.end, self.events))
        return self._data


def current_run_path(recorder=None, out_dir=None):
    """(该看的那局记录, 是不是正在记)。记录器在记就看这局, 否则看最近一局。"""
    run = getattr(recorder, 'run', None)
    live_path = getattr(run, 'path', None)
    if live_path and os.path.exists(live_path):
        return live_path, True
    last = getattr(recorder, 'last_path', None)
    if last and os.path.exists(last):
        return last, False
    files = list_run_files(out_dir or getattr(recorder, 'out_dir', None) or default_out_dir())
    return (files[-1], False) if files else (None, False)


def team_members(data):
    """[(号位, 类名, 显示名)] 按号位排。"""
    members = []
    for char in data.header.get('team') or ():
        if isinstance(char, dict) and char.get('i') is not None:
            slot = char.get('i')
            members.append((slot, char.get('cls') or char.get('n'), data.char_name(slot)))
    return sorted(members, key=lambda m: m[0])


def field_segments(data, window=None):
    """(起, 止, [(t0, t1, 号位)]): 在场段, window 给秒数时只要最后 window 秒。号位 -1 是 HUD 不在 (大招演出等)。"""
    end = data.duration
    start = max(0.0, end - window) if window else 0.0
    segments = []
    for span in data.field:
        if span.t1 <= start:
            continue
        segments.append((max(span.t0, start), span.t1, span.value))
    return start, end, segments


def current_slot(data):
    """现在 (最后一段) 谁在场; HUD 不在时算最后一个看到的人。"""
    for span in reversed(data.field):
        if span.value != HUD_HIDDEN:
            return span.value
    return None


def field_time(data):
    """{号位: 在场秒数}, 只算认准了的段。"""
    totals = {}
    for span in data.field:
        if span.certain and span.value != HUD_HIDDEN:
            totals[span.value] = totals.get(span.value, 0.0) + span.t1 - span.t0
    return totals


def field_changes(data):
    """[(时刻, 号位)]: 每次换人, 只算认准了的段, 大招演出 HUD 消失又回来不算换人。"""
    changes, previous = [], None
    for span in data.field:
        if span.certain and span.value != HUD_HIDDEN and span.value != previous:
            changes.append((span.t0, span.value))
            previous = span.value
    return changes


def cycle_laps(data, limit=6, max_period=16):
    """按上场顺序的重复周期分圈: (每圈从谁上场开始, 每圈换几次人, [(第几圈, 开始, 时长)])。

    不按某一个人分: 一圈里上场两次的人按他分会得到「45 秒、7 秒」交替。
    这里找换人顺序从某处起一直重复的最短周期 (开场轴不重复, 自然被排在外面), 覆盖最长的那个周期胜出。
    找不到至少两整圈的周期返回 (None, 0, [])。
    """
    changes = field_changes(data)
    sequence = [slot for _, slot in changes]
    count = len(sequence)
    best = None  # (覆盖的换人次数, -周期, 起点)
    for period in range(2, max_period + 1):
        start = count - period
        while start > 0 and sequence[start - 1 + period] == sequence[start - 1]:
            start -= 1
        if start < 0 or (count - 1 - start) // period < 2:
            continue
        key = (count - start, -period, start)
        if best is None or key > best:
            best = key
    if best is None:
        return None, 0, []
    _, period, start = best
    period = -period
    laps = []
    for number, anchor in enumerate(range(start, count - period, period), 1):
        laps.append((number, changes[anchor][0], changes[anchor + period][0] - changes[anchor][0]))
    return sequence[start], period, laps[-limit:]


def recent_laps(data, limit=6):
    """(分圈用的号位, [(第几圈, 开始, 时长)]): 按每圈只上场一次的人分圈, 只要最后 limit 圈。"""
    slot = data.default_lap_slot()
    if slot is None:
        return None, []
    laps = data.laps(slot)
    first = max(0, len(laps) - limit)
    return slot, [(i + 1, start, duration) for i, (start, duration) in enumerate(laps) if i >= first]


def latency_summary(data):
    """{'switch': (中位 ms, 次数), 'lib': (中位 ms, 次数)}; 没样本时中位是 None。"""
    result = analyse(data.events)
    return {name: (median_ms(samples), len(samples)) for name, samples in result.items()}
