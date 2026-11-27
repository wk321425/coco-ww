"""后台帧被动 HUD 遥测提取(不阻塞战斗热路径, 仅依赖 cv2 + numpy)。

在 MediaWriter 存帧时顺便从原图抽取:
- hp: Boss 血条长度占比 (0~1), 无血条返回 None
- g:  右侧 3 格队友头像外圈白环角度占比 [g0, g1, g2] (0~1)
- f:  共鸣回路条右端高亮区白像素占比 (0~1)
- sk: 技能栏 E / R / Q 图标白色高亮占比 [e, r, q] (0~1)
"""
import cv2
import numpy as np

# 与 CombatCheck.boss_health_color 一致 (BGR 顺序)
BOSS_HP_LOWER = np.array([4, 30, 245], dtype=np.uint8)
BOSS_HP_UPPER = np.array([75, 185, 255], dtype=np.uint8)

# 3840x2160 基准下的 UI 坐标
SKILL_BOXES_3840 = (
    (3185, 1877, 135, 113),  # E (box_resonance)
    (3572, 1877, 126, 113),  # R (box_liberation)
    (3371, 1877, 135, 117),  # Q (box_echo)
)


def _as_bgr(frame):
    if frame is None or not hasattr(frame, 'shape') or len(frame.shape) < 3:
        return None
    if frame.shape[2] == 4:
        return frame[:, :, :3]
    return frame[:, :, :3] if frame.shape[2] > 3 else frame


def compute_slot_glow(frame, slot):
    """右侧队伍栏第 slot 格(0 起)头像外面细白环落在同一半径上的上半圈角度占比(0~1)。"""
    bgr = _as_bgr(frame)
    if bgr is None:
        return 0.0
    h, w = bgr.shape[:2]
    if h <= 0 or w <= 0:
        return 0.0
    s = h / 2160.0
    cx = w - (3840.0 - 3586.5) * s
    cy = (500.0 + 264.0 * slot) * s
    rad = int(round(125.0 * s)) + 3
    xa, ya = int(cx) - rad, int(cy) - rad
    if xa < 0 or ya < 0 or xa + 2 * rad + 1 > w or ya + 2 * rad + 1 > h:
        return 0.0
    crop = bgr[ya:ya + 2 * rad + 1, xa:xa + 2 * rad + 1]
    white = np.ascontiguousarray(crop.min(axis=2)).astype(np.float32)
    polar = cv2.warpPolar(white, (rad, 360), (cx - xa, cy - ya), rad, cv2.WARP_POLAR_LINEAR)
    rows = polar[225:331]
    d = max(1, int(round(4.5 * s)))
    r = np.arange(int(80 * s), int(118 * s))
    if r.size == 0 or r[0] < d or r[-1] + d >= rows.shape[1]:
        return 0.0
    ridge = rows[:, r] - np.maximum(rows[:, r - d], rows[:, r + d])
    k = ridge.argmax(axis=1)
    hit = ridge[np.arange(len(rows)), k] > 40
    if not hit.any():
        return 0.0
    hist = np.bincount(r[k][hit], minlength=int(r[-1]) + 2)
    win = max(2, int(round(4 * s)))
    if len(hist) < win:
        return 0.0
    return float(np.convolve(hist, np.ones(win), 'valid').max()) / len(rows)


def extract_boss_hp(frame):
    """提取顶部 Boss 血条占比 (0~1), 无血条返回 None。"""
    bgr = _as_bgr(frame)
    if bgr is None:
        return None
    h, w = bgr.shape[:2]
    s = h / 2160.0
    x0 = max(0, int(round(w / 2.0 - (1920.0 - 1269.0) * s)))
    x1 = min(w, int(round(w / 2.0 + (2533.0 - 1920.0) * s)))
    y0 = max(0, int(round(58.0 * s)))
    y1 = min(h, int(round(200.0 * s)))
    if x1 <= x0 or y1 <= y0:
        return None
    crop = bgr[y0:y1, x0:x1]
    mask = cv2.inRange(crop, BOSS_HP_LOWER, BOSS_HP_UPPER)
    min_cols = max(8, int(round(16.0 * s)))
    row_hits = np.count_nonzero(mask, axis=1)
    peak_row = int(np.argmax(row_hits))
    if int(row_hits[peak_row]) < min_cols:
        return None
    band = max(4, int(round(14.0 * s)))
    sub_mask = mask[max(0, peak_row - band):min(mask.shape[0], peak_row + band + 1), :]
    min_rows = max(2, int(round(3.0 * s)))
    col_hits = np.count_nonzero(sub_mask, axis=0) >= min_rows
    cols = np.flatnonzero(col_hits)
    if cols.size < min_cols:
        return None
    max_gap = max(6, int(round(18.0 * s)))
    segments = np.split(cols, np.flatnonzero(np.diff(cols) > max_gap) + 1)
    best = max(segments, key=lambda seg: seg.size)
    best_hits = int(best.size)
    best_span = int(best[-1] - best[0] + 1)
    if best_hits < min_cols or (best_hits / max(1, best_span)) < 0.65:
        return None
    full_w = max(1.0, 1180.0 * s)
    return min(1.0, round(best_span / full_w, 3))


def extract_forte_bar_lit(frame):
    """提取共鸣回路条右端满条高亮区 (2251..2311, 1993..2016) 纯白像素占比。"""
    bgr = _as_bgr(frame)
    if bgr is None:
        return 0.0
    h, w = bgr.shape[:2]
    s = h / 2160.0
    x0 = max(0, int(round(w / 2.0 + (2251.0 - 1920.0) * s)))
    x1 = min(w, int(round(w / 2.0 + (2311.0 - 1920.0) * s)))
    y0 = max(0, int(round(h - (2160.0 - 1993.0) * s)))
    y1 = min(h, int(round(h - (2160.0 - 2016.0) * s)))
    if x1 <= x0 or y1 <= y0:
        return 0.0
    crop = bgr[y0:y1, x0:x1]
    return round(float((crop.min(axis=2) >= 200).mean()), 2)


def extract_skill_highlights(frame):
    """提取技能栏 [E, R, Q] 图标纯白像素占比 (0~1)。"""
    bgr = _as_bgr(frame)
    if bgr is None:
        return [0.0, 0.0, 0.0]
    h, w = bgr.shape[:2]
    s = h / 2160.0
    out = []
    for bx, by, bw, bh in SKILL_BOXES_3840:
        x0 = max(0, int(round(w - (3840.0 - bx) * s)))
        x1 = min(w, int(round(w - (3840.0 - bx - bw) * s)))
        y0 = max(0, int(round(h - (2160.0 - by) * s)))
        y1 = min(h, int(round(h - (2160.0 - by - bh) * s)))
        if x1 <= x0 or y1 <= y0:
            out.append(0.0)
        else:
            crop = bgr[y0:y1, x0:x1]
            out.append(round(float((crop.min(axis=2) >= 235).mean()), 3))
    return out


def extract_hud_snapshot(frame):
    """从单帧原图抽取紧凑 HUD 状态快照。"""
    bgr = _as_bgr(frame)
    if bgr is None:
        return None
    return {
        'hp': extract_boss_hp(bgr),
        'g': [round(compute_slot_glow(bgr, i), 2) for i in range(3)],
        'f': extract_forte_bar_lit(bgr),
        'sk': extract_skill_highlights(bgr),
    }


def hud_changed(prev, cur, prev_t=None, cur_t=None, min_heartbeat=0.5):
    """判断两帧 HUD 快照是否有值得落盘的变化(或到达心跳间隔)。"""
    if cur is None:
        return False
    if prev is None:
        return True
    if prev_t is not None and cur_t is not None and cur_t - prev_t >= min_heartbeat:
        return True
    hp0, hp1 = prev.get('hp'), cur.get('hp')
    if (hp0 is None) != (hp1 is None):
        return True
    if hp0 is not None and abs(hp0 - hp1) >= 0.02:
        return True
    if any(abs(a - b) >= 0.12 for a, b in zip(prev.get('g') or (), cur.get('g') or ())):
        return True
    if abs(float(prev.get('f', 0)) - float(cur.get('f', 0))) >= 0.12:
        return True
    if any(abs(a - b) >= 0.05 for a, b in zip(prev.get('sk') or (), cur.get('sk') or ())):
        return True
    return False
