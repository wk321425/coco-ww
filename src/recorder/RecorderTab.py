"""「跑轴复盘」页(C1 影院布局): 画面放大当主角, 左上角叠此刻信息, 能逐帧、按事件跳、慢放;
右边「此刻」列这一刻的读屏、前后日志、接下来; 底下整局分圈条 + 在场/按键/提醒三条时间线。
读屏泳道和事件表(带分圈对比)收着, 要查代码时再展开。"""
import bisect
import collections
import html
import json
import os
import subprocess
import threading
import time

from PySide6.QtCore import QAbstractTableModel, QModelIndex, QPoint, QPointF, QRect, QRectF, QSize, \
    QSortFilterProxyModel, Qt, QTimer, Signal
from PySide6.QtGui import QBrush, QColor, QFont, QFontMetrics, QImage, QKeySequence, QPainter, QPen, QShortcut
from PySide6.QtWidgets import QAbstractItemView, QApplication, QFrame, QHBoxLayout, QHeaderView, QMenu, QSizePolicy, QSplitter, \
    QStackedWidget, QTableWidgetItem, QToolTip, QVBoxLayout, QWidget

from .diagnostics import analyze_run, compare_runs, format_diagnostics
from .feedback import (FEEDBACK_DIR, FRAMES_KEEP, FRAMES_NONE, FRAMES_STANDARD, FeedbackPlan, build_feedback,
                       import_feedback)
from .media import EXPORT_DIR, LOW_WIDTH, MediaIndex, clear_exports, export_usage
from .recorder import HOLDER_ATTR, default_out_dir
from .runs import (HUD_HIDDEN, LOG_LEVELS, READ_KINDS, RunData, Span, char_label, describe, detail_lines, headline,
                   import_root, list_imported_runs, list_runs, source_text, video_clock, video_pending)
from .screenrec import load_video_info, video_info_path

# coco-ww 用宿主自带的控件库(ok.ui.qt.kit): 按钮、下拉框、文字用它的类, 其余原生控件靠
# theme.install() 给这一页套上的样式表上色。插件时代的 qfluentwidgets 新环境里没有。
from PySide6.QtWidgets import QCheckBox as CheckBox, QLineEdit as SearchLineEdit, \
    QPlainTextEdit as PlainTextEdit, QScrollArea as ScrollArea, QSlider as Slider, QTableView as TableView, \
    QTableWidget as TableWidget

from ok.ui.qt.kit.buttons import Button as PushButton
from ok.ui.qt.kit.cards import Card
from ok.ui.qt.kit.dialogs import confirm
from ok.ui.qt.kit.feedback import show_toast
from ok.ui.qt.kit.inputs import ComboBox
from ok.ui.qt.kit.labels import Label as BodyLabel
from ok.ui.qt.kit.theme import theme

# 下面几个名字是 qfluentwidgets 才有的, 留成 None 让旧的分支判断照常走原生那一路
FluentIcon = SegmentedWidget = MessageBoxBase = SubtitleLabel = None


def isDarkTheme():
    return theme.is_dark()


LABEL_W = 210
# 平时(C1 影院布局)底下只画在场/按键/提醒三条, 泳道名窄一点; 点「全部泳道」才画读屏、日志这些
COMPACT_LABEL_W = 62
RULER_H = 24
PREFS_FILE = '_tab_prefs.json'
# 每 0.5 秒看一眼是不是刚收尾(刚收尾马上刷新), 平时 3 秒读一次盘
TICK_MS = 500
REFRESH_TICKS = 6
SLOT_COLORS = ['#4C8DF6', '#F28C38', '#3DB37A', '#B05CD6']
HIDDEN_COLOR = '#8A8A8A'
KEY_COLORS = {'E': '#20A4A4', 'R': '#E04848', 'Q': '#8E5BD8', 'F': '#D4A017', 'T': '#6B8E23'}
LEVEL_COLORS = {30: '#E69A28', 40: '#E04848', 50: '#E04848'}
# 分圈对比里比这一列中位数慢这么多秒就标出来
LAP_SLOW = 1.0
SLOW_COLOR = '#E8871E'
# 拖红线到可视区边上这么近就开始滚, 每次最多滚这么多像素
DRAG_EDGE = 16
DRAG_SCROLL = 40


def _add_item(box, text, data):
    # Fluent 的 ComboBox.addItem 第二个参数是图标
    if FluentIcon is not None:
        box.addItem(text, userData=data)
    else:
        box.addItem(text, data)


def _lap_item(text, t=None, slow=False):
    item = QTableWidgetItem(text)
    item.setTextAlignment(Qt.AlignCenter)
    if t is not None:
        item.setData(Qt.UserRole, t)
    if slow:
        item.setForeground(QBrush(QColor(SLOW_COLOR)))
        font = item.font()
        font.setBold(True)
        item.setFont(font)
    return item


class Lane:
    __slots__ = ('kind', 'label', 'y', 'h', 'items', 'starts')

    def __init__(self, kind, label, h, items=None):
        self.kind = kind
        self.label = label
        self.y = 0
        self.h = h
        self.items = items or []
        self.starts = []


def _start(item):
    if isinstance(item, dict):
        return item.get('t', 0)
    return item.t0 if isinstance(item, Span) else item.t


def _end(item):
    if isinstance(item, dict):
        return item.get('t2', item.get('t', 0))
    return item.t1


class TimelineCanvas(QWidget):
    """时间线。平时只画在场、按键(键盘和鼠标一条)、提醒(WARN 以上的日志和打点)三条;
    full=True(「全部泳道」)时画全: 出招、鼠标单独一条、每一处读屏、日志。"""
    timeClicked = Signal(float)
    timeDragged = Signal(float)
    eventClicked = Signal(object)
    # 能看到的时间段变了(滚动、缩放、换局): (开始秒, 结束秒), 整局进度条上画框
    viewChanged = Signal(float, float)

    def __init__(self, scroll_area):
        super().__init__()
        self.scroll_area = scroll_area
        self.run = None
        self.lanes = []
        self.pps = 60.0
        self.cursor_t = None
        self.dark = False
        self.full = False
        self.label_w = COMPACT_LABEL_W
        self._label_rows = {}
        self._dragging = False
        self._drag_moved = False
        self.setMouseTracking(True)
        scroll_area.horizontalScrollBar().valueChanged.connect(self.update)
        scroll_area.verticalScrollBar().valueChanged.connect(self.update)
        scroll_area.horizontalScrollBar().valueChanged.connect(lambda _: self._emit_view())

    # ---------- 数据 ----------

    def set_run(self, run):
        self.run = run
        self.cursor_t = None
        self.lanes = self._build_lanes(run) if run is not None else []
        self._resize()
        self.update()
        self._emit_view()

    def set_full(self, full):
        """切换「全部泳道」; 看的时间段和红线不变。"""
        if full == self.full:
            return
        anchor = self.cursor_t
        self.full = full
        self.label_w = LABEL_W if full else COMPACT_LABEL_W
        self.lanes = self._build_lanes(self.run) if self.run is not None else []
        self._resize()
        if anchor is not None:
            self.center_on(anchor)
        self.update()
        self._emit_view()

    def content_height(self):
        return (self.lanes[-1].y + self.lanes[-1].h + 12) if self.lanes else 120

    def _build_lanes(self, run):
        keys = [m for m in run.input_groups if m.event.get('a') not in ('click', 'md', 'mu', 'wheel')]
        mouse = [m for m in run.input_groups if m.event.get('a') in ('click', 'md', 'mu', 'wheel')]
        key_holds = [h for h in run.holds if h.event.get('a') not in ('md', 'mu')]
        mouse_holds = [h for h in run.holds if h.event.get('a') in ('md', 'mu')]
        if not self.full:
            alerts = run.marks + [e for e in run.logs if (e.get('l') or 0) >= 30]
            lanes = [
                Lane('field', '在场', 22, run.field),
                Lane('keys', '按键', 30, key_holds + mouse_holds + keys + mouse),
                Lane('alerts', '提醒', 16, alerts),
            ]
        else:
            lanes = [
                Lane('field', '在场', 22, run.field),
                Lane('perform', '出招(perform)', 16, run.perform),
                Lane('keys', '按键', 28, key_holds + keys),
                Lane('mouse', '鼠标', 22, mouse_holds + mouse),
            ]
            if run.marks:
                lanes.append(Lane('marks', '打点', 18, run.marks))
            if getattr(run, 'huds', None):
                lanes.append(Lane('hud', '遥测(HUD)', 20, run.huds))
            for row in run.reads:
                lanes.append(Lane('read', row.label, 14, row.events))
            if run.logs:
                lanes.append(Lane('logs', '日志', 18, run.logs))
        y = RULER_H + 4
        for lane in lanes:
            lane.y = y
            y += lane.h + 3
            lane.items.sort(key=_start)
            lane.starts = [_start(item) for item in lane.items]
        return lanes

    def _resize(self):
        duration = self.run.duration if self.run is not None else 0
        height = self.content_height() if self.lanes else 120
        self.resize(int(self.label_w + max(1.0, duration) * self.pps + 60), int(height))

    def set_zoom(self, pps, anchor_t=None):
        bar = self.scroll_area.horizontalScrollBar()
        viewport = self.scroll_area.viewport().width()
        if anchor_t is None:
            anchor_t = self.t_at(bar.value() + self.label_w + (viewport - self.label_w) / 2)
        offset = self.x_at(anchor_t) - bar.value()
        self.pps = max(5.0, min(2000.0, pps))
        self._resize()
        bar.setValue(int(self.x_at(anchor_t) - offset))
        self.update()
        self._emit_view()

    def visible_range(self):
        bar = self.scroll_area.horizontalScrollBar()
        viewport = self.scroll_area.viewport().width()
        return max(0.0, self.t_at(bar.value() + self.label_w)), max(0.0, self.t_at(bar.value() + viewport))

    def _emit_view(self):
        self.viewChanged.emit(*self.visible_range())

    def ensure_visible(self, t, margin=0.15):
        """t 跑出能看到的那段(或者贴边了)就滚过去, 放着播时红线不会跑出去。"""
        lo, hi = self.visible_range()
        pad = (hi - lo) * margin
        if not lo + pad <= t <= hi - pad:
            bar = self.scroll_area.horizontalScrollBar()
            viewport = self.scroll_area.viewport().width()
            bar.setValue(int(self.x_at(t) - self.label_w - (viewport - self.label_w) * 0.3))

    def set_cursor(self, t):
        if t != self.cursor_t:
            self._move_cursor(t)

    def x_at(self, t):
        return self.label_w + t * self.pps

    def t_at(self, x):
        return (x - self.label_w) / self.pps

    def center_on(self, t):
        bar = self.scroll_area.horizontalScrollBar()
        viewport = self.scroll_area.viewport().width()
        bar.setValue(int(self.x_at(t) - self.label_w - (viewport - self.label_w) / 2))
        self.cursor_t = t
        self.update()

    # ---------- 画 ----------

    def _colors(self):
        dark = isDarkTheme()
        return {
            'bg': QColor('#202020' if dark else '#FFFFFF'),
            'lane': QColor('#2A2A2A' if dark else '#F5F6F8'),
            'text': QColor('#E6E6E6' if dark else '#202020'),
            'dim': QColor('#8C8C8C' if dark else '#8A8F98'),
            'grid': QColor('#3A3A3A' if dark else '#E3E5E8'),
            'header': QColor('#262626' if dark else '#FAFAFB'),
            'off': QColor('#555555' if dark else '#D5D8DD'),
        }

    def paintEvent(self, event):
        painter = QPainter(self)
        colors = self._colors()
        rect = event.rect()
        painter.fillRect(rect, colors['bg'])
        if self.run is None:
            painter.setPen(colors['dim'])
            painter.drawText(self.rect(), Qt.AlignCenter, '还没有记录。开着「跑轴记录」打一局自动战斗, 打完点「刷新」。')
            return
        small = QFont(self.font())
        small.setPointSizeF(max(7.0, small.pointSizeF() * 0.85))
        painter.setFont(small)
        metrics = QFontMetrics(small)
        t_lo = max(0.0, self.t_at(rect.left()) - 0.5)
        t_hi = self.t_at(rect.right()) + 0.5
        self._draw_grid(painter, colors, rect, t_lo, t_hi)
        self._label_rows = {}
        for lane in self.lanes:
            if lane.y > rect.bottom() or lane.y + lane.h < rect.top():
                continue
            painter.fillRect(QRectF(max(rect.left(), self.label_w), lane.y, rect.width(), lane.h), colors['lane'])
            draw = getattr(self, '_draw_' + lane.kind)
            for item in self._visible(lane, t_lo, t_hi):
                draw(painter, colors, metrics, lane, item)
        if self.cursor_t is not None:
            painter.setPen(QPen(QColor('#E04848'), 1))
            x = self.x_at(self.cursor_t)
            painter.drawLine(QPointF(x, rect.top()), QPointF(x, rect.bottom()))
        self._draw_sticky(painter, colors, metrics, t_lo, t_hi)

    def _visible(self, lane, t_lo, t_hi):
        starts = lane.starts
        if lane.kind in ('keys', 'mouse', 'alerts'):
            # 按住的段可能很长, 和点按混在一起, 数量也不多, 直接全扫
            for item in lane.items:
                if _start(item) <= t_hi and _end(item) >= t_lo:
                    yield item
            return
        i = max(0, bisect.bisect_left(starts, t_lo) - 1)
        while i < len(starts) and starts[i] <= t_hi:
            item = lane.items[i]
            if _end(item) >= t_lo:
                yield item
            i += 1

    def _draw_grid(self, painter, colors, rect, t_lo, t_hi):
        step = self._tick_step()
        painter.setPen(QPen(colors['grid'], 1))
        t = int(t_lo / step) * step
        while t <= t_hi:
            x = self.x_at(t)
            painter.drawLine(QPointF(x, rect.top()), QPointF(x, rect.bottom()))
            t += step

    def _tick_step(self):
        for step in (0.05, 0.1, 0.25, 0.5, 1, 2, 5, 10, 30, 60):
            if step * self.pps >= 70:
                return step
        return 120

    def _span_rect(self, lane, t0, t1, min_w=2.0):
        x0 = self.x_at(t0)
        return QRectF(x0, lane.y + 1, max(min_w, self.x_at(t1) - x0), lane.h - 2)

    def _text_in(self, painter, color, metrics, rect, text):
        if rect.width() < 14:
            return
        painter.setPen(color)
        painter.drawText(rect.adjusted(3, 0, -2, 0), Qt.AlignVCenter | Qt.AlignLeft,
                         metrics.elidedText(text, Qt.ElideRight, int(rect.width() - 5)))

    def _draw_field(self, painter, colors, metrics, lane, span):
        color = QColor(HIDDEN_COLOR if span.value == HUD_HIDDEN else SLOT_COLORS[span.value % len(SLOT_COLORS)])
        rect = self._span_rect(lane, span.t0, span.t1)
        if span.shaky:
            painter.fillRect(rect, QBrush(color, Qt.Dense5Pattern))
            self._text_in(painter, colors['text'], metrics, rect, span.label)
            return
        if span.seen < span.t1 - 0.02:
            # 最后一次看到之后轴没再看 HUD, 这一截画淡: 实际可能早就变了
            faded = QColor(color)
            faded.setAlpha(70)
            painter.fillRect(rect, faded)
            seen = self._span_rect(lane, span.t0, span.seen)
            painter.fillRect(seen, color)
            self._text_in(painter, QColor('#FFFFFF') if seen.width() >= 30 else colors['text'], metrics, rect,
                          span.label)
            return
        painter.fillRect(rect, color)
        self._text_in(painter, QColor('#FFFFFF'), metrics, rect, span.label)

    def _draw_perform(self, painter, colors, metrics, lane, span):
        slot = span.event.get('i') if span.event else 0
        color = QColor(SLOT_COLORS[(slot or 0) % len(SLOT_COLORS)])
        color.setAlpha(110)
        rect = self._span_rect(lane, span.t0, span.t1)
        painter.fillRect(rect, color)
        self._text_in(painter, colors['text'], metrics, rect, span.label + (f' ({span.value})' if span.value else ''))

    def _key_color(self, label):
        if label.startswith('切'):
            for slot, name in self.run.names.items():
                if label == '切' + (name or ''):
                    return QColor(SLOT_COLORS[slot % len(SLOT_COLORS)])
        return QColor(KEY_COLORS.get(label.replace('按住', '').replace('(没松)', ''), '#7A8088'))

    def _draw_keys(self, painter, colors, metrics, lane, item):
        self._draw_input(painter, colors, metrics, lane, item)

    def _draw_mouse(self, painter, colors, metrics, lane, item):
        self._draw_input(painter, colors, metrics, lane, item)

    def _draw_input(self, painter, colors, metrics, lane, item):
        if isinstance(item, Span):
            color = self._key_color(item.label)
            color.setAlpha(90)
            rect = self._span_rect(lane, item.t0, item.t1)
            painter.fillRect(rect, color)
            self._text_in(painter, colors['text'], metrics, rect, item.label)
            return
        color = self._key_color(item.label)
        x = self.x_at(item.t)
        if item.count > 1:
            # 连按: 起止之间一条淡底, 标 ×N
            band = QColor(color)
            band.setAlpha(55)
            painter.fillRect(self._span_rect(lane, item.t, item.t1), band)
        painter.setPen(QPen(color, 2))
        painter.drawLine(QPointF(x, lane.y + 1), QPointF(x, lane.y + lane.h - 1))
        if self.pps >= 25 and (item.label != 'A' or item.count > 1):
            # 切人只写名字前几个字母, 免得压住紧跟着的 E/R; 全名在悬停提示里
            text = '切' + item.label[1:5] if item.label.startswith('切') else item.label
            if item.count > 1:
                text += f'×{item.count}'
            # 挨得近的标签放上一行, 两行都占了就不写(悬停还看得到)
            rows = self._label_rows.setdefault(lane.kind, [float('-inf'), float('-inf')])
            baselines = [lane.y + lane.h - 6] + ([lane.y + 12] if lane.h >= 26 else [])
            for row, baseline in enumerate(baselines):
                if x + 3 >= rows[row]:
                    painter.setPen(colors['text'])
                    painter.drawText(QPointF(x + 3, baseline), text)
                    rows[row] = x + 3 + metrics.horizontalAdvance(text) + 4
                    break

    def _draw_marks(self, painter, colors, metrics, lane, event):
        x = self.x_at(event['t'])
        painter.setPen(QPen(QColor('#D4A017'), 2))
        painter.drawLine(QPointF(x, lane.y + 1), QPointF(x, lane.y + lane.h - 1))
        painter.setPen(colors['text'])
        painter.drawText(QPointF(x + 3, lane.y + lane.h - 5), str(event.get('name')))

    def _read_color(self, event):
        kind, value = event.get('k'), event.get('v')
        if kind in ('find', 'feat'):
            return QColor('#3DB37A') if event.get('ok') else QColor(self._colors()['off'])
        if not isinstance(value, (int, float)):
            return QColor('#7A8088')
        if kind == 'cd':
            return QColor('#F28C38') if value > 0 else QColor('#3DB37A')
        if kind == 'con':
            color = QColor('#4C8DF6')
            color.setAlpha(255 if value >= 0.99 else int(50 + 170 * max(0.0, min(1.0, value))))
            return color
        color = QColor('#B05CD6')
        color.setAlpha(int(50 + 205 * max(0.0, min(1.0, value * 2))))
        return color

    def _draw_read(self, painter, colors, metrics, lane, event):
        t0 = event['t']
        t1 = event.get('t2', t0)
        rect = self._span_rect(lane, t0, t1, min_w=3.0)
        painter.fillRect(rect, self._read_color(event))

    def _draw_alerts(self, painter, colors, metrics, lane, event):
        if event.get('e') == 'mark':
            self._draw_marks(painter, colors, metrics, lane, event)
        else:
            self._draw_logs(painter, colors, metrics, lane, event)

    def _draw_hud(self, painter, colors, metrics, lane, event):
        if self.run is not None and not self.run.is_hud_visible_at(event['t']):
            return
        x = self.x_at(event['t'])
        bar_w = max(2.0, min(6.0, 0.25 * self.pps))
        hp = event.get('hp')
        if isinstance(hp, (int, float)):
            frac = max(0.0, min(1.0, float(hp)))
            if frac > 0:
                h = max(2.0, (lane.h - 4) * frac)
                hp_color = QColor('#C94A4A')
                hp_color.setAlpha(185)
                painter.fillRect(QRectF(x, lane.y + lane.h - 2 - h, bar_w, h), hp_color)
        f_val = event.get('f')
        if isinstance(f_val, (int, float)) and float(f_val) >= 0.15:
            painter.fillRect(QRectF(x, lane.y + lane.h * 0.45, max(2.0, min(4.0, bar_w)), 3.0), QColor('#36C2CF'))
        glows = self.run.off_field_glows(event) if self.run is not None else event.get('g')
        if isinstance(glows, (list, tuple)) and glows and max(glows) >= 0.35:
            painter.setPen(QPen(QColor('#F0B429'), 2))
            painter.drawLine(QPointF(x, lane.y + 1), QPointF(x, lane.y + 6))

    def _draw_logs(self, painter, colors, metrics, lane, event):
        x = self.x_at(event['t'])
        color = QColor(LEVEL_COLORS.get(event.get('l'), colors['dim'].name()))
        painter.setPen(QPen(color, 1))
        painter.drawLine(QPointF(x, lane.y + 3), QPointF(x, lane.y + lane.h - 3))

    def _draw_sticky(self, painter, colors, metrics, t_lo, t_hi):
        hbar = self.scroll_area.horizontalScrollBar().value()
        vbar = self.scroll_area.verticalScrollBar().value()
        viewport = self.scroll_area.viewport()
        # 左边的泳道名
        painter.fillRect(QRectF(hbar, vbar, self.label_w, viewport.height()), colors['header'])
        for lane in self.lanes:
            if lane.y + lane.h < vbar + RULER_H or lane.y > vbar + viewport.height():
                continue
            rect = QRectF(hbar + 6, lane.y, self.label_w - 10, lane.h)
            painter.setPen(colors['text'] if lane.kind != 'read' else colors['dim'])
            painter.drawText(rect, Qt.AlignVCenter | Qt.AlignLeft,
                             metrics.elidedText(lane.label, Qt.ElideMiddle, int(rect.width())))
        # 顶上的时间刻度
        painter.fillRect(QRectF(hbar, vbar, viewport.width(), RULER_H), colors['header'])
        step = self._tick_step()
        t = int(t_lo / step) * step
        painter.setPen(colors['dim'])
        while t <= t_hi:
            x = self.x_at(t)
            if x >= hbar + self.label_w:
                label = f'{t:.2f}'.rstrip('0').rstrip('.') + 's'
                painter.drawLine(QPointF(x, vbar + RULER_H - 6), QPointF(x, vbar + RULER_H))
                painter.drawText(QPointF(x + 3, vbar + RULER_H - 8), label)
            t += step
        if self.cursor_t is not None and self.x_at(self.cursor_t) >= hbar + self.label_w:
            painter.setPen(QColor('#E04848'))
            painter.drawText(QPointF(self.x_at(self.cursor_t) + 3, vbar + 10), f'{self.cursor_t:.3f}s')
        painter.fillRect(QRectF(hbar, vbar, self.label_w, RULER_H), colors['header'])
        if self.label_w >= 150:
            painter.setPen(colors['dim'])
            painter.drawText(QRectF(hbar + 6, vbar, self.label_w - 10, RULER_H), Qt.AlignVCenter | Qt.AlignLeft,
                             'Ctrl+滚轮缩放  点或拖红线定位')

    # ---------- 鼠标 ----------

    def _hit(self, pos):
        x, y = pos.x(), pos.y()
        hbar = self.scroll_area.horizontalScrollBar().value()
        if self.run is None or x < hbar + self.label_w:
            return None, None
        t = self.t_at(x)
        tolerance = 5 / self.pps
        for lane in self.lanes:
            if lane.y <= y <= lane.y + lane.h:
                best, best_d = None, None
                for item in self._visible(lane, t - tolerance, t + tolerance):
                    t0, t1 = _start(item), _end(item)
                    d = 0 if t0 <= t <= t1 else min(abs(t - t0), abs(t - t1))
                    if d <= tolerance and (best_d is None or d < best_d):
                        best, best_d = item, d
                return lane, best
        return None, None

    def _tooltip(self, lane, item):
        run = self.run
        if isinstance(item, dict):
            kind, text = describe(run, item)
            source = source_text(item)
            return f"{item.get('t', 0):.3f}s  {kind}  {text}" + (f'\n{source}' if source else '')
        if isinstance(item, Span):
            text = f'{item.label}  {item.t0:.3f}–{item.t1:.3f}s  ({item.t1 - item.t0:.3f}s)'
            if lane.kind == 'field' and item.shaky:
                text += ('\nHUD 淡入淡出, 只认到一个号码: 框架把第一个没认到的格子当当前角色, 这一段认的人不可信'
                         '\n分圈、在场时长、按键归属都不算它')
            if lane.kind == 'field' and item.seen < item.t1 - 0.02:
                text += f'\n最后一次看到 {item.seen:.3f}s, 之后 {item.t1 - item.seen:.2f}s 轴没看 HUD(画淡的部分)'
            if item.event is not None and lane.kind in ('keys', 'mouse'):
                source = source_text(item.event)
                if source:
                    text += '\n' + source
            return text
        kind, text = describe(run, item.event)
        if item.count > 1:
            text = f'{item.label} 连按 {item.count} 下  {item.t:.3f}–{item.t1:.3f}s'
        if item.hidden and item.slot is not None:
            text += f'  (HUD 不在或没认全, 算{run.char_name(item.slot)}的)'
        source = source_text(item.event)
        return f'{item.t:.3f}s  {text}' + (f'\n{source}' if source else '')

    def _cursor_rect(self, t):
        if t is None:
            return None
        vbar = self.scroll_area.verticalScrollBar().value()
        # 竖线加顶上那个时间标签
        return QRect(int(self.x_at(t)) - 4, vbar, 96, self.scroll_area.viewport().height())

    def _move_cursor(self, t):
        # 拖的时候只重画新旧两条线附近, 不整片重画
        old, self.cursor_t = self.cursor_t, t
        for rect in (self._cursor_rect(old), self._cursor_rect(t)):
            if rect is not None:
                self.update(rect)

    def _near_cursor(self, x):
        return self.cursor_t is not None and abs(x - self.x_at(self.cursor_t)) <= 5

    def _drag_t(self, x):
        """拖到可视区左右边上顺带滚动。"""
        bar = self.scroll_area.horizontalScrollBar()
        left = bar.value() + self.label_w
        right = bar.value() + self.scroll_area.viewport().width()
        if x > right - DRAG_EDGE:
            bar.setValue(int(bar.value() + min(DRAG_SCROLL, x - (right - DRAG_EDGE))))
        elif x < left + DRAG_EDGE:
            bar.setValue(int(bar.value() - min(DRAG_SCROLL, left + DRAG_EDGE - x)))
        x = max(x, bar.value() + self.label_w)
        return max(0.0, min(self.run.duration, self.t_at(x)))

    def mouseMoveEvent(self, event):
        x = event.position().x()
        if self._dragging:
            if event.buttons() & Qt.LeftButton:
                self._drag_moved = True
                self._move_cursor(self._drag_t(x))
                self.timeDragged.emit(self.cursor_t)
            return
        self.setCursor(Qt.SizeHorCursor if self._near_cursor(x) else Qt.ArrowCursor)
        lane, item = self._hit(event.position())
        if item is not None:
            QToolTip.showText(event.globalPosition().toPoint(), self._tooltip(lane, item), self)
        else:
            QToolTip.hideText()

    def mousePressEvent(self, event):
        x = event.position().x()
        if event.button() != Qt.LeftButton or self.run is None \
                or x < self.scroll_area.horizontalScrollBar().value() + self.label_w:
            return
        # 点哪儿红线到哪儿, 按住不放就能拖
        self._dragging, self._drag_moved = True, False
        self.setCursor(Qt.SizeHorCursor)
        QToolTip.hideText()
        self._move_cursor(max(0.0, self.t_at(x)))
        self.timeClicked.emit(self.cursor_t)
        _, item = self._hit(event.position())
        if isinstance(item, dict):
            self.eventClicked.emit(item)

    def mouseReleaseEvent(self, event):
        if not self._dragging:
            return
        self._dragging = False
        self.setCursor(Qt.SizeHorCursor if self._near_cursor(event.position().x()) else Qt.ArrowCursor)
        if self._drag_moved:
            # 松手才对表格: 拖的途中选行、滚表格太费
            self.timeClicked.emit(self.cursor_t)

    def wheelEvent(self, event):
        if event.modifiers() & Qt.ControlModifier:
            factor = 1.25 if event.angleDelta().y() > 0 else 0.8
            self.set_zoom(self.pps * factor, self.t_at(event.position().x()))
            event.accept()
            return
        super().wheelEvent(event)


BOX_COLORS = {'found': '#3DB37A', 'missed': '#E8871E', 'color': '#B05CD6', 'mark': '#D4A017'}
# 光标前后这么久内读过的框都叠到画面上(读屏是一段一段合并的, 一帧 0.25 秒)
BOX_WINDOW = 0.15
FRAME_CACHE = 24
# 两帧隔这么久就说明轴那段时间没取画面
FRAME_GAP_NOTE = 0.6
# 画面缩放: 按「全图」的倍数算, 滚一格乘/除这么多
ZOOM_MAX = 8.0
ZOOM_STEP = 1.25
# 放大到这么多倍时, 标清存的局提醒一下会糊
ZOOM_BLUR_NOTE = 2.0
# 常看的几处(占画面的比例 x, y, 宽, 高), 按 16:9 鸣潮默认 HUD 估的
ZOOM_PRESETS = [
    ('技能栏', (0.70, 0.84, 0.30, 0.16)),
    ('协奏', (0.34, 0.83, 0.32, 0.17)),
    ('队伍', (0.86, 0.15, 0.14, 0.40)),
    ('Boss', (0.30, 0.0, 0.40, 0.12)),
]
# 画面底色(影院: 黑边)
STAGE_BG = '#0E0E12'
# 播放: 每这么多毫秒走一步; 速度可选(画面一秒 4 帧, 慢放看得清)
PLAY_MS = 40
SPEEDS = (0.25, 0.5, 1.0, 2.0)
DEFAULT_SPEED = 0.5
# 「此刻」: 日志看前后几秒、最多几条; 读屏最多列几处; 接下来列几条
NOW_LOG_WINDOW = 1.5
NOW_LOGS = 6
NOW_READS = 8
NOW_NEXT = 5
# 画面左上角「操作」那一行: 只看这么多秒内按的键, 最多这么多个, 最后一个按下不到 OP_FLASH 秒时亮着
OPS_WINDOW = 2.0
OPS_MAX = 6
OP_FLASH = 0.3


def _num_text(value):
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return str(value)
    return f'{value:.2f}'


class FrameView(QWidget):
    """一帧画面(C1 影院布局里的主角), 上面叠这一刻读过的框和左上角的「此刻」信息。框是原分辨率坐标, 按画面宽度缩。
    能放大看: 滚轮以鼠标为中心缩放, 左键拖动平移, 双击回到全图; 放大时右上角有小地图, 点它跳过去。
    换帧时缩放和位置不变(逐帧看同一块)。"""
    zoomChanged = Signal(float)

    def __init__(self):
        super().__init__()
        self.image = None
        self.source_w = None
        self.boxes = []
        self.message = ''
        # 左上角叠的信息: {'title', 'time', 'field': (名字, 颜色, 文字), 'ops': [(键, 几秒前, 切给几号位或 None)],
        #                  'hold': (名字, 进度 0~1, 文字)}
        self.overlay = None
        # 这帧之后轴好久没取画面时的提醒, 叠在信息框最下面
        self.frame_note = ''
        self.show_boxes = True
        self.show_overlay = True
        self.zoom = 1.0
        # 视野中心落在画面的哪(0~1, 0~1)
        self.center = (0.5, 0.5)
        self._drag = None
        self._minimap_drag = False
        self.setMinimumSize(320, 180)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.setMouseTracking(True)

    def sizeHint(self):
        return QSize(800, 450)

    def set_frame(self, image, source_w=None, boxes=(), message=''):
        self.image, self.source_w, self.boxes, self.message = image, source_w, list(boxes), message
        self._update_cursor()
        self.update()

    def set_overlay(self, overlay, note=None):
        self.overlay = overlay
        if note is not None:
            self.frame_note = note
        self.update()

    # ---------- 缩放 ----------

    def fit_rect(self):
        """全图时画面占的地方(按比例塞进控件, 居中)。"""
        if self.image is None or self.image.isNull():
            return None
        iw, ih = self.image.width(), self.image.height()
        scale = min(self.width() / iw, self.height() / ih)
        w, h = iw * scale, ih * scale
        return QRectF((self.width() - w) / 2, (self.height() - h) / 2, w, h)

    def _clamped(self, center, w, h):
        """视野不出画面: 放大后比控件还宽(高)的那一边, 中心离边至少半个控件; 没铺满的那一边居中。"""
        out = []
        for c, size, view in ((center[0], w, self.width()), (center[1], h, self.height())):
            if size <= view:
                out.append(0.5)
            else:
                half = view / (2 * size)
                out.append(min(1 - half, max(half, c)))
        return tuple(out)

    def image_rect(self):
        fit = self.fit_rect()
        if fit is None or self.zoom <= 1.0:
            return fit
        w, h = fit.width() * self.zoom, fit.height() * self.zoom
        cx, cy = self._clamped(self.center, w, h)
        return QRectF(self.width() / 2 - cx * w, self.height() / 2 - cy * h, w, h)

    def set_zoom(self, zoom, center=None, anchor=None):
        """zoom 按全图的倍数(1 是全图)。center 给了就把那一点(0~1)放到中间;
        anchor 给了(控件坐标)就让鼠标底下那一点缩放前后不动。"""
        fit = self.fit_rect()
        zoom = max(1.0, min(ZOOM_MAX, float(zoom)))
        if fit is None:
            self.zoom = zoom
            self.center = center or self.center
            self.zoomChanged.emit(self.zoom)
            return
        old = self.image_rect()
        w, h = fit.width() * zoom, fit.height() * zoom
        if center is None and anchor is not None and old is not None:
            u = (anchor.x() - old.x()) / old.width()
            v = (anchor.y() - old.y()) / old.height()
            center = ((self.width() / 2 - anchor.x()) / w + u, (self.height() / 2 - anchor.y()) / h + v)
        elif center is None:
            center = self._clamped(self.center, old.width(), old.height()) if old is not None else self.center
        self.zoom = zoom
        self.center = (0.5, 0.5) if zoom <= 1.0 else self._clamped(center, w, h)
        self._update_cursor()
        self.update()
        self.zoomChanged.emit(self.zoom)

    def zoom_to(self, region):
        """放大到画面里的一块 (x, y, 宽, 高), 都是 0~1 的比例; 刚好装下。"""
        x, y, w, h = region
        self.set_zoom(min(1.0 / max(w, 1e-3), 1.0 / max(h, 1e-3)), center=(x + w / 2, y + h / 2))

    def reset_zoom(self):
        self.set_zoom(1.0, center=(0.5, 0.5))

    def minimap_rect(self):
        fit = self.fit_rect()
        if fit is None or self.zoom <= 1.0:
            return None
        w = min(200.0, max(96.0, self.width() * 0.22))
        h = w * self.image.height() / self.image.width()
        return QRectF(self.width() - w - 8, 8, w, h)

    def _visible_part(self):
        """视野框在画面里的比例 (x, y, 宽, 高)。"""
        rect = self.image_rect()
        x0 = max(0.0, -rect.x() / rect.width())
        y0 = max(0.0, -rect.y() / rect.height())
        x1 = min(1.0, (self.width() - rect.x()) / rect.width())
        y1 = min(1.0, (self.height() - rect.y()) / rect.height())
        return x0, y0, x1 - x0, y1 - y0

    def _minimap_jump(self, pos):
        mini = self.minimap_rect()
        u = min(1.0, max(0.0, (pos.x() - mini.x()) / mini.width()))
        v = min(1.0, max(0.0, (pos.y() - mini.y()) / mini.height()))
        self.set_zoom(self.zoom, center=(u, v))

    def _update_cursor(self):
        if self._drag is not None:
            self.setCursor(Qt.ClosedHandCursor)
        elif self.zoom > 1.0 and self.image is not None:
            self.setCursor(Qt.OpenHandCursor)
        else:
            self.unsetCursor()

    def wheelEvent(self, event):
        if self.fit_rect() is None:
            return super().wheelEvent(event)
        steps = event.angleDelta().y() / 120
        if not steps:
            return
        self.set_zoom(self.zoom * ZOOM_STEP ** steps, anchor=event.position())
        event.accept()

    def mousePressEvent(self, event):
        if event.button() != Qt.LeftButton or self.fit_rect() is None:
            return super().mousePressEvent(event)
        mini = self.minimap_rect()
        if mini is not None and mini.contains(event.position()):
            self._minimap_drag = True
            self._minimap_jump(event.position())
        elif self.zoom > 1.0:
            self._drag = (event.position(), self.center)
            self._update_cursor()
        event.accept()

    def mouseMoveEvent(self, event):
        if self._minimap_drag:
            self._minimap_jump(event.position())
        elif self._drag is not None:
            start, center = self._drag
            rect = self.image_rect()
            delta = event.position() - start
            self.center = self._clamped((center[0] - delta.x() / rect.width(), center[1] - delta.y() / rect.height()),
                                        rect.width(), rect.height())
            self.update()
        else:
            mini = self.minimap_rect()
            if mini is not None and mini.contains(event.position()):
                self.setCursor(Qt.PointingHandCursor)
            else:
                self._update_cursor()
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.LeftButton:
            self._drag = None
            self._minimap_drag = False
            self._update_cursor()
        super().mouseReleaseEvent(event)

    def mouseDoubleClickEvent(self, event):
        if event.button() == Qt.LeftButton and self.fit_rect() is not None:
            self.reset_zoom()
            event.accept()
            return
        super().mouseDoubleClickEvent(event)

    # ---------- 画 ----------

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.SmoothPixmapTransform)
        painter.fillRect(self.rect(), QColor(STAGE_BG))
        target = self.image_rect()
        if target is None:
            painter.setPen(QColor('#8C8C8C'))
            painter.drawText(self.rect().adjusted(12, 0, -12, 0), Qt.AlignCenter | Qt.TextWordWrap, self.message)
        else:
            painter.drawImage(target, self.image)
            if self.source_w and self.show_boxes:
                self._paint_boxes(painter, target)
            if self.zoom > 1.0:
                self._paint_minimap(painter)
        if self.show_overlay and (self.overlay or self.frame_note):
            self._paint_overlay(painter)

    def _paint_minimap(self, painter):
        mini = self.minimap_rect()
        painter.fillRect(mini.adjusted(-2, -2, 2, 2), QColor(0, 0, 0, 170))
        painter.drawImage(mini, self.image)
        x, y, w, h = self._visible_part()
        view = QRectF(mini.x() + x * mini.width(), mini.y() + y * mini.height(), w * mini.width(), h * mini.height())
        painter.setBrush(Qt.NoBrush)
        painter.setPen(QPen(theme.color('accent'), 2))
        painter.drawRect(view)

    def _paint_overlay(self, painter):
        """左上角一块半透明的「此刻」: 第几圈 + 时间 / 谁在场 + 这一段多久 / 最近按了什么 / 按住什么、按了多久。"""
        o = self.overlay or {}
        painter.save()
        painter.setRenderHint(QPainter.Antialiasing)
        base = QFont(self.font())
        size = base.pointSizeF() if base.pointSizeF() > 0 else 9.0
        bold = QFont(base)
        bold.setBold(True)
        mono = QFont('Consolas')
        mono.setPointSizeF(size)
        mono.setBold(True)
        small = QFont(base)
        small.setPointSizeF(max(7.0, size * 0.9))
        fm, fb, fmono, fs = QFontMetrics(base), QFontMetrics(bold), QFontMetrics(mono), QFontMetrics(small)
        text_color, dim = QColor('#EDEDF2'), QColor('#A6A6B3')
        pad, gap, bar_w = 10, 6, 72
        limit = max(160, int(self.width() * 0.6))
        rows = []
        title, clock = o.get('title') or '', o.get('time') or ''
        if title or clock:
            width = fb.horizontalAdvance(title) + (8 if title else 0) + fmono.horizontalAdvance(clock)
            rows.append(('head', max(fb.height(), fmono.height()), width))
        field = o.get('field')
        if field:
            chip_w = fb.horizontalAdvance(field[0]) + 14
            rows.append(('field', fb.height() + 6, chip_w + 8 + fm.horizontalAdvance(field[2])))
        ops, chips = o.get('ops'), []
        if ops is not None:
            # 一个键一块: 文字 + 左右留白, 切人的前面多一个号位颜色的点; 太宽从最早的扔
            for text, age, slot in ops:
                chips.append((text, age, slot, fb.horizontalAdvance(text) + 12 + (10 if slot is not None else 0)))
            op_tail = f'{ops[-1][1]:.2f}s前' if ops else f'{OPS_WINDOW:g} 秒内没按键'
            op_head = fm.horizontalAdvance('操作') + 8
            while len(chips) > 1 and op_head + sum(c[3] + 4 for c in chips) + 2 + fs.horizontalAdvance(op_tail) > limit:
                chips.pop(0)
            rows.append(('ops', fm.height() + 4,
                         op_head + sum(c[3] + 4 for c in chips) + 2 + fs.horizontalAdvance(op_tail)))
        hold = o.get('hold')
        if hold:
            rows.append(('hold', fm.height(), fm.horizontalAdvance(hold[0]) + 8 + bar_w + 8 + fm.horizontalAdvance(hold[2])))
        note = fs.elidedText(self.frame_note, Qt.ElideRight, limit) if self.frame_note else ''
        if note:
            rows.append(('note', fs.height(), fs.horizontalAdvance(note)))
        if not rows:
            painter.restore()
            return
        width = min(limit, max(w for _, _, w in rows)) + 2 * pad
        height = sum(h for _, h, _ in rows) + gap * (len(rows) - 1) + 2 * pad - 2
        box = QRectF(10, 10, width, height)
        painter.setPen(QPen(QColor(255, 255, 255, 22), 1))
        painter.setBrush(QColor(12, 12, 16, 205))
        painter.drawRoundedRect(box, 9, 9)
        y = box.y() + pad - 1
        x0 = box.x() + pad
        for kind, h, _ in rows:
            if kind == 'head':
                x = x0
                if title:
                    painter.setFont(bold)
                    painter.setPen(text_color)
                    painter.drawText(QRectF(x, y, fb.horizontalAdvance(title) + 2, h), Qt.AlignVCenter | Qt.AlignLeft,
                                     title)
                    x += fb.horizontalAdvance(title) + 8
                painter.setFont(mono)
                painter.setPen(theme.color('accent'))
                painter.drawText(QRectF(x, y, fmono.horizontalAdvance(clock) + 4, h), Qt.AlignVCenter | Qt.AlignLeft,
                                 clock)
            elif kind == 'field':
                name, color, text = field
                chip = QRectF(x0, y, fb.horizontalAdvance(name) + 14, h)
                painter.setPen(Qt.NoPen)
                painter.setBrush(QColor(color))
                painter.drawRoundedRect(chip, 5, 5)
                painter.setFont(bold)
                painter.setPen(QColor('#101014'))
                painter.drawText(chip, Qt.AlignCenter, name)
                painter.setFont(base)
                painter.setPen(text_color)
                rest = box.right() - pad - chip.right() - 8
                painter.drawText(QRectF(chip.right() + 8, y, rest, h), Qt.AlignVCenter | Qt.AlignLeft,
                                 fm.elidedText(text, Qt.ElideRight, int(rest)))
            elif kind == 'ops':
                painter.setFont(base)
                painter.setPen(dim)
                painter.drawText(QRectF(x0, y, op_head, h), Qt.AlignVCenter | Qt.AlignLeft, '操作')
                x = x0 + op_head
                for i, (text, age, slot, chip_w) in enumerate(chips):
                    # 越早按的越淡; 最后一个刚按下时整块亮起来, 播放时看得出「这一下按了」
                    fade = 1.0 - 0.55 * min(1.0, age / OPS_WINDOW)
                    fresh = i == len(chips) - 1 and age < OP_FLASH
                    chip = QRectF(x, y, chip_w, h)
                    painter.setPen(Qt.NoPen)
                    painter.setBrush(QColor('#EDEDF2') if fresh else QColor(255, 255, 255, int(16 + 30 * fade)))
                    painter.drawRoundedRect(chip, 5, 5)
                    tx = x + 6
                    if slot is not None:
                        dot = QColor(SLOT_COLORS[slot % len(SLOT_COLORS)])
                        painter.setBrush(dot)
                        painter.drawEllipse(QRectF(tx, y + h / 2 - 3, 6, 6))
                        tx += 10
                    painter.setFont(bold)
                    painter.setPen(QColor('#101014') if fresh else QColor(237, 237, 242, int(255 * fade)))
                    painter.drawText(QRectF(tx, y, chip.right() - tx, h), Qt.AlignCenter, text)
                    x += chip_w + 4
                painter.setFont(small)
                painter.setPen(dim)
                painter.drawText(QRectF(x + 2, y, fs.horizontalAdvance(op_tail) + 4, h), Qt.AlignVCenter | Qt.AlignLeft,
                                 op_tail)
            elif kind == 'hold':
                name, frac, text = hold
                painter.setFont(base)
                painter.setPen(dim)
                label_w = fm.horizontalAdvance(name)
                painter.drawText(QRectF(x0, y, label_w + 2, h), Qt.AlignVCenter | Qt.AlignLeft, name)
                bar = QRectF(x0 + label_w + 8, y + h / 2 - 2, bar_w, 4)
                painter.setPen(Qt.NoPen)
                painter.setBrush(QColor(255, 255, 255, 36))
                painter.drawRoundedRect(bar, 2, 2)
                painter.setBrush(QColor('#C9C9D3'))
                painter.drawRoundedRect(QRectF(bar.x(), bar.y(), bar.width() * max(0.0, min(1.0, frac)), 4), 2, 2)
                painter.setPen(text_color)
                painter.drawText(QRectF(bar.right() + 8, y, fm.horizontalAdvance(text) + 4, h),
                                 Qt.AlignVCenter | Qt.AlignLeft, text)
            else:
                painter.setFont(small)
                painter.setPen(theme.color('warning'))
                painter.drawText(QRectF(x0, y, width - 2 * pad, h), Qt.AlignVCenter | Qt.AlignLeft, note)
            y += h + gap
        painter.restore()

    def _paint_boxes(self, painter, target):
        k = target.width() / self.source_w
        small = QFont(self.font())
        small.setPointSizeF(max(7.0, small.pointSizeF() * 0.8))
        painter.setFont(small)
        metrics = QFontMetrics(small)
        for (x, y, w, h), color, label in self.boxes:
            rect = QRectF(target.x() + x * k, target.y() + y * k, max(2.0, w * k), max(2.0, h * k))
            painter.setPen(QPen(QColor(color), 2))
            painter.setBrush(Qt.NoBrush)
            painter.drawRect(rect)
            if label:
                text = metrics.elidedText(label, Qt.ElideRight, 160)
                back = QRectF(rect.x(), rect.y() - metrics.height() - 1, metrics.horizontalAdvance(text) + 6,
                              metrics.height())
                if back.y() < max(0.0, target.y()):
                    back.moveTop(rect.bottom() + 1)
                fill = QColor(color)
                fill.setAlpha(200)
                painter.fillRect(back, fill)
                painter.setPen(QColor('#FFFFFF'))
                painter.drawText(back.adjusted(3, 0, 0, 0), Qt.AlignVCenter | Qt.AlignLeft, text)


class CropView(QWidget):
    """读屏那块原图, 按整数倍放大(不插值, 像素看得清)。"""

    def __init__(self):
        super().__init__()
        self.image = None
        self.setFixedHeight(120)
        self.setMinimumWidth(120)

    def set_image(self, image):
        self.image = image
        self.update()

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.fillRect(self.rect(), QColor('#1A1A1A' if isDarkTheme() else '#E9EBEE'))
        if self.image is None or self.image.isNull():
            return
        iw, ih = self.image.width(), self.image.height()
        fit = min(self.width() / iw, self.height() / ih)
        scale = max(1, int(fit)) if fit >= 1 else fit
        w, h = iw * scale, ih * scale
        painter.drawImage(QRectF((self.width() - w) / 2, (self.height() - h) / 2, w, h), self.image)


class FramePanel(QWidget):
    """画面这一块: 上面一排缩放, 中间画面(左上角叠此刻信息, 读屏框), 下面播放条。"""
    stepped = Signal(float)
    eventStep = Signal(int)
    playToggled = Signal()

    def __init__(self):
        super().__init__()
        self.run = None
        self.media = None
        self.index = -1
        self.t = 0.0
        self.boxed = []
        self.speed = DEFAULT_SPEED
        self._cache = collections.OrderedDict()
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(6)
        # 缩放这一排: 全图 + 常看的几处, 右边是放大倍数和这局存的分辨率
        zoom_bar = QHBoxLayout()
        zoom_bar.setSpacing(4)
        self.zoom_buttons = []
        for text, region in [('全图', None)] + ZOOM_PRESETS:
            button = PushButton(text, variant='subtle', size='small')
            button.setToolTip('回到整张画面(双击画面也行)' if region is None else f'放大看{text}那一块')
            button.clicked.connect(lambda _=False, r=region: self.view.reset_zoom() if r is None else self.view.zoom_to(r))
            zoom_bar.addWidget(button)
            self.zoom_buttons.append(button)
        zoom_bar.addStretch(1)
        self.zoom_label = BodyLabel('')
        zoom_bar.addWidget(self.zoom_label)
        layout.addLayout(zoom_bar)
        self.view = FrameView()
        layout.addWidget(self.view, 1)

        bar = QHBoxLayout()
        bar.setSpacing(4)
        self.prev_event = PushButton('◀ 事件', size='small')
        self.prev_event.setToolTip('跳到上一个事件: 切人上场、按键、松开按住的键、打点')
        self.prev_button = PushButton('', icon='chevron-left', size='small')
        self.prev_button.setToolTip('上一帧 (←)')
        self.play_button = PushButton('', icon='play', variant='primary', size='small')
        self.play_button.setToolTip('从红线处往后播 / 暂停 (空格)')
        self.next_button = PushButton('', icon='chevron-right', size='small')
        self.next_button.setToolTip('下一帧 (→)')
        self.next_event = PushButton('事件 ▶', size='small')
        self.next_event.setToolTip('跳到下一个事件: 切人上场、按键、松开按住的键、打点')
        self.prev_event.clicked.connect(lambda: self.eventStep.emit(-1))
        self.next_event.clicked.connect(lambda: self.eventStep.emit(1))
        self.prev_button.clicked.connect(lambda: self.step(-1))
        self.next_button.clicked.connect(lambda: self.step(1))
        self.play_button.clicked.connect(self.playToggled.emit)
        for button in (self.prev_event, self.prev_button, self.play_button, self.next_button, self.next_event):
            bar.addWidget(button)
        bar.addSpacing(8)
        self.speed_buttons = {}
        for speed in SPEEDS:
            button = PushButton(f'{speed:g}×', variant='subtle', size='small')
            button.setToolTip('播放速度(画面每秒 4 帧, 慢放看得清)')
            button.clicked.connect(lambda _=False, s=speed: self.set_speed(s))
            bar.addWidget(button)
            self.speed_buttons[speed] = button
        bar.addSpacing(8)
        self.boxes_check = CheckBox('读屏框')
        self.boxes_check.setChecked(True)
        self.boxes_check.setToolTip('画面上叠这一刻前后 0.15 秒读过的框')
        self.boxes_check.toggled.connect(self._toggle_boxes)
        self.info_check = CheckBox('此刻信息')
        self.info_check.setChecked(True)
        self.info_check.setToolTip('画面左上角叠第几圈、谁在场、这一段多久、按住什么')
        self.info_check.toggled.connect(self._toggle_info)
        bar.addWidget(self.boxes_check)
        bar.addWidget(self.info_check)
        bar.addStretch(1)
        self.frame_label = BodyLabel('')
        self.frame_label.setTextInteractionFlags(Qt.TextSelectableByMouse)
        bar.addWidget(self.frame_label)
        layout.addLayout(bar)
        self.view.zoomChanged.connect(lambda _: self._update_zoom_label())
        self.set_speed(DEFAULT_SPEED)

    def set_speed(self, speed):
        self.speed = speed
        for value, button in self.speed_buttons.items():
            button.set_variant('tonal' if value == speed else 'subtle')

    def set_playing(self, playing):
        self.play_button.set_icon('pause' if playing else 'play')

    def _toggle_boxes(self, on):
        self.view.show_boxes = on
        self.view.update()

    def _toggle_info(self, on):
        self.view.show_overlay = on
        self.view.update()

    def set_overlay(self, overlay):
        self.view.set_overlay(overlay)

    def set_run(self, run, media):
        self.run, self.media = run, media
        self._cache.clear()
        self.boxed = []
        self.view.reset_zoom()
        if run is not None:
            self.boxed = [e for e in run.events if e.get('e') in ('read', 'mark')
                          and (isinstance(e.get('box'), list) or isinstance(e.get('rb'), list))]
        self.show_time(0.0)

    def has_frames(self):
        return self.media is not None and bool(self.media.frames)

    def show_time(self, t):
        self.t = t
        if not self.has_frames():
            self.index = -1
            self.frame_label.setText('')
            if self.run is None:
                message = ''
            else:
                message = ('这局没存画面。「跑轴记录」设置里开着「整局存画面」打的局才有, 只留最近几局。')
            self.view.frame_note = ''
            self.view.set_frame(None, message=message)
            self._update_zoom_label()
            return
        self._show(self.media.frame_index(t), t)

    def step(self, delta):
        if not self.has_frames():
            return
        index = max(0, min(len(self.media.frames) - 1, self.index + delta))
        self.stepped.emit(self.media.frames[index]['t'])

    def refresh_caption(self):
        if self.has_frames() and self.index >= 0:
            self._show(self.index, self.t)

    def _update_zoom_label(self):
        has = self.view.image is not None and not self.view.image.isNull()
        for button in self.zoom_buttons:
            button.setEnabled(has)
        if not has:
            self.zoom_label.setText('')
            return
        image = self.view.image
        text = f'{self.view.zoom * 100:.0f}% · {image.width()}×{image.height()}'
        tip = ('放大倍数 · 这局画面存的分辨率(「跑轴记录」设置里的「整局画面清晰度」)\n'
               '滚轮缩放(以鼠标为中心), 拖动平移, 双击回到全图; 换帧时缩放和位置不变')
        blurry = self.view.zoom >= ZOOM_BLUR_NOTE and image.width() <= LOW_WIDTH
        if blurry:
            text += ' · 放大会糊'
            tip = (f'这局按 {image.width()}×{image.height()} 存的, 放大后小字看不清。'
                   '「跑轴记录」设置里把「整局画面清晰度」调高, 下一局起生效\n' + tip)
        self.zoom_label.setText(text)
        self.zoom_label.setToolTip(tip)
        self.zoom_label.setStyleSheet(f"color: {theme.color('warning').name()};" if blurry else '')

    def _show(self, index, t):
        frames = self.media.frames
        self.index = index
        entry = frames[index]
        caption = f"帧 {index + 1}/{len(frames)} · {entry['t']:.2f}s"
        clock = video_clock(self.run, t) if self.run is not None else None
        if clock:
            caption += f' · {clock}'  # 剪视频时拿这个时间去录屏里找
        self.frame_label.setText(caption)
        gap = (frames[index + 1]['t'] if index + 1 < len(frames) else t) - entry['t']
        note = ''
        if gap > FRAME_GAP_NOTE and t - entry['t'] > FRAME_GAP_NOTE / 2:
            # 画面是轴自己取的帧: 定时连点、等演出这类不读屏的时候就没有, 别把旧帧当成那一刻
            note = f"这是 {entry['t']:.2f}s 的帧, 之后 {gap:.1f}s 轴没取画面(定时操作或等演出时不读屏)"
        self.view.frame_note = note
        size = self.run.header.get('size') if self.run is not None else None
        source_w = size[0] if isinstance(size, list) and size else None
        image = self._image(entry)
        self.view.set_frame(image, source_w, self._boxes_at(t),
                            message='' if image is not None else '这一帧读不出来(文件不完整)')
        self._update_zoom_label()

    def _image(self, entry):
        key = entry['o']
        image = self._cache.get(key)
        if image is None:
            try:
                image = QImage.fromData(self.media.read(entry))
            except OSError:
                return None
            if image.isNull():
                return None
            self._cache[key] = image
            if len(self._cache) > FRAME_CACHE:
                self._cache.popitem(last=False)
        else:
            self._cache.move_to_end(key)
        return image

    def _boxes_at(self, t):
        boxes = []
        for event in self.boxed:
            t0 = event.get('t', 0)
            if not t0 - BOX_WINDOW <= t <= event.get('t2', t0) + BOX_WINDOW:
                continue
            name, value = event.get('name'), event.get('v')
            box, found_box = event.get('box'), event.get('rb')
            if event.get('e') == 'mark':
                color, label = BOX_COLORS['mark'], f'{name}={_num_text(value)}'
            elif event.get('k') == 'color':
                color, label = BOX_COLORS['color'], f'{name or "颜色"} {_num_text(value)}'
            elif event.get('ok'):
                color, label = BOX_COLORS['found'], f'{name} {_num_text(value)}'
            else:
                color, label = BOX_COLORS['missed'], f'{name} 没找到'
            if isinstance(box, list) and len(box) == 4:
                boxes.append((box, color, label))
                label = ''
            if isinstance(found_box, list) and len(found_box) == 4:
                boxes.append((found_box, BOX_COLORS['found'], label))
        return boxes[:40]


class LapInfo:
    """按某个角色上场分圈的结果; 整局进度条、画面左上角「第几圈」「本段多久 / 中位」共用。"""

    def __init__(self, run=None, slot=None):
        self.slot = slot
        self.columns, self.laps = run.lap_breakdown(slot) if run is not None and slot is not None else ([], [])
        self.baselines = RunData.lap_baselines(self.columns, self.laps)[0] if self.laps else []
        self.starts = [lap[0] for lap in self.laps]

    def lap_at(self, t):
        """第几圈(从 0 数); 第一圈之前是 -1, 最后一圈之后是 len(laps); 没分圈 None。"""
        if not self.laps:
            return None
        i = bisect.bisect_right(self.starts, t) - 1
        if i < 0:
            return -1
        start, total, _ = self.laps[i]
        return i if t < start + total else len(self.laps)

    def over(self, i):
        """第 i 圈比同样上场顺序那几圈的中位数慢多少秒; 比不了 None。"""
        base = self.baselines[i]
        if base is None or base[-1] is None:
            return None
        return self.laps[i][1] - base[-1]

    def segment_at(self, i, t):
        """第 i 圈里 t 落在谁那一段: (开始, 时长, 同顺序几圈这一段的中位数或 None)。"""
        if i is None or not 0 <= i < len(self.laps):
            return None
        for key, (t0, duration) in self.laps[i][2].items():
            if t0 <= t < t0 + duration:
                base = self.baselines[i]
                median = base[self.columns.index(key)] if base is not None and key in self.columns else None
                return t0, duration, median
        return None


class LapStrip(QWidget):
    """整局一条: 按分圈的角色切成一圈一圈, 比同顺序中位数慢的圈标红; 没分圈时按谁在场上色。
    框出底下时间线正看着的那段, 红线是光标; 点或拖跳过去。"""
    timePicked = Signal(float)

    def __init__(self):
        super().__init__()
        self.run = None
        # (开始, 结束, 字, 慢不慢, 悬停提示, 号位或 None)
        self.segments = []
        self.view = None
        self.cursor_t = None
        self._dragging = False
        self.setFixedHeight(24)
        self.setMouseTracking(True)

    def set_run(self, run, info):
        self.run = run
        segments = []
        if run is not None and info.laps:
            first = info.laps[0][0]
            if first > 0.05:
                segments.append((0.0, first, '开场', False, f'开场  0–{first:.2f}s', None))
            for i, (start, total, _) in enumerate(info.laps):
                over = info.over(i)
                slow = over is not None and over >= LAP_SLOW
                tip = f'第 {i + 1} 圈  {start:.2f}–{start + total:.2f}s  用时 {total:.2f}s'
                if over is not None:
                    tip += f'\n比同样上场顺序那几圈的中位数{"慢" if over >= 0 else "快"} {abs(over):.2f}s'
                segments.append((start, start + total, f'{i + 1}' + (f' · +{over:.1f}s' if slow else ''), slow, tip,
                                 None))
            end = info.laps[-1][0] + info.laps[-1][1]
            if run.duration - end > 0.05:
                segments.append((end, run.duration, '', False, f'最后一圈之后  {end:.2f}–{run.duration:.2f}s', None))
        elif run is not None:
            for span in run.field:
                segments.append((span.t0, span.t1, span.label, False,
                                 f'{span.label}  {span.t0:.2f}–{span.t1:.2f}s', span.value))
        self.segments = segments
        self.setToolTip('' if run is None or info.laps else '没分圈(右上角「分圈按」选一个角色), 这里按谁在场上色')
        self.update()

    def set_view(self, t0, t1):
        self.view = (t0, t1)
        self.update()

    def set_cursor(self, t):
        self.cursor_t = t
        self.update()

    def _k(self):
        duration = self.run.duration if self.run is not None else 0
        return self.width() / duration if duration > 0 else 0

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)
        h = self.height()
        painter.setPen(Qt.NoPen)
        painter.setBrush(theme.color('control'))
        painter.drawRoundedRect(QRectF(self.rect()), 5, 5)
        k = self._k()
        if not k:
            return
        small = QFont(self.font())
        small.setPointSizeF(max(7.0, small.pointSizeF() * 0.85))
        painter.setFont(small)
        metrics = QFontMetrics(small)
        dark = isDarkTheme()
        for t0, t1, text, slow, _, slot in self.segments:
            rect = QRectF(t0 * k, 0, max(1.0, (t1 - t0) * k - 1), h)
            if slot is not None:
                color = QColor(HIDDEN_COLOR if slot == HUD_HIDDEN else SLOT_COLORS[slot % len(SLOT_COLORS)])
                color.setAlpha(150)
                ink = theme.color('text')
            elif slow:
                color, ink = QColor(248, 113, 113, 70), QColor('#F8A5A5' if dark else '#C2410C')
            elif text and text != '开场':
                color, ink = theme.color('control_hover'), theme.color('text_secondary')
            else:
                color, ink = theme.color('surface_alt'), theme.color('text_tertiary')
            painter.fillRect(rect, color)
            if text and rect.width() >= 14:
                painter.setPen(ink)
                painter.drawText(rect, Qt.AlignCenter, metrics.elidedText(text, Qt.ElideRight, int(rect.width() - 4)))
        if self.view is not None:
            v0, v1 = self.view
            box = QRectF(v0 * k, 1, max(4.0, (v1 - v0) * k), h - 2)
            fill = theme.color('text')
            fill.setAlpha(22)
            painter.setBrush(fill)
            painter.setPen(QPen(theme.color('text'), 1.5))
            painter.drawRoundedRect(box, 4, 4)
        if self.cursor_t is not None:
            painter.setPen(QPen(QColor('#E04848'), 2))
            x = self.cursor_t * k
            painter.drawLine(QPointF(x, 0), QPointF(x, h))

    def _pick(self, x):
        k = self._k()
        if k:
            self.timePicked.emit(max(0.0, min(self.run.duration, x / k)))

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton and self._k():
            self._dragging = True
            self._pick(event.position().x())

    def mouseMoveEvent(self, event):
        if self._dragging and event.buttons() & Qt.LeftButton:
            self._pick(event.position().x())
            return
        k = self._k()
        if not k:
            return
        t = event.position().x() / k
        tip = next((s[4] for s in self.segments if s[0] <= t < s[1]), '')
        if tip:
            QToolTip.showText(event.globalPosition().toPoint(), tip, self)

    def mouseReleaseEvent(self, event):
        self._dragging = False


def build_moments(run):
    """能跳的「事件」和「接下来」里列的东西: [(秒, HTML)]。切人上场、HUD 不在、按键(连按算一下)、松开按住的键、打点。
    日志不算: WARN 常常一秒刷好几条, 放进来按「下一个事件」就只在日志里打转(日志在「前后 1.5 秒日志」和提醒那条里看)。"""
    dim = theme.color('text_tertiary').name()
    moments = []
    previous = None
    for span in run.field:
        if span.certain and span.value != previous:
            color = SLOT_COLORS[span.value % len(SLOT_COLORS)]
            moments.append((span.t0, f'<span style="color:{color}">●</span> {html.escape(span.label)} 上场'))
            previous = span.value
        elif span.value == HUD_HIDDEN and span.t1 - span.t0 >= 0.5:
            moments.append((span.t0, f'<span style="color:{dim}">HUD 不在 {span.t1 - span.t0:.2f}s</span>'))
    for mark in run.input_groups:
        text = html.escape(mark.label) + (f' ×{mark.count}' if mark.count > 1 else '')
        moments.append((mark.t, text))
    for hold in run.holds:
        label = hold.label.replace('按住', '', 1).replace('(没松)', '')
        if hold.label.endswith('(没松)'):
            continue
        moments.append((hold.t1, f'松开 {html.escape(label)} <span style="color:{dim}">共按住 '
                                 f'{hold.t1 - hold.t0:.2f}s</span>'))
    for event in run.marks:
        moments.append((event['t'], f"打点 {html.escape(str(event.get('name')))} = "
                                    f"{html.escape(_num_text(event.get('v')))}"))
    moments.sort(key=lambda m: m[0])
    return moments


def _short(text, limit):
    text = ' '.join(str(text).split())
    return text if len(text) <= limit else text[:limit - 1] + '…'


class NowPanel(Card):
    """右边「此刻」: 光标这一刻读了哪些屏、前后 1.5 秒的日志、接下来发生什么; 点读屏事件时下面显示读的那块原图。
    底下两个开关: 事件表(在下面展开事件表和分圈对比)、全部泳道(时间线画全读屏和日志)。"""
    drawerToggled = Signal(bool)
    lanesToggled = Signal(bool)

    def __init__(self):
        super().__init__()
        self.run = None
        self.media = None
        self.moments = []
        self._moment_ts = []
        self._read_starts = []
        self._log_ts = []
        self.drawer_on = False
        self.lanes_on = False
        outer = QVBoxLayout(self)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(0)
        head = QHBoxLayout()
        head.setContentsMargins(14, 10, 14, 4)
        head.setSpacing(8)
        head.addWidget(BodyLabel('此刻', role='strong'))
        self.time_label = BodyLabel('', role='secondary')
        head.addWidget(self.time_label)
        head.addStretch(1)
        outer.addLayout(head)

        scroll = ScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        scroll.setStyleSheet('QScrollArea, QScrollArea > QWidget > QWidget { background: transparent; }')
        body = QWidget()
        layout = QVBoxLayout(body)
        layout.setContentsMargins(14, 4, 14, 10)
        layout.setSpacing(4)

        def section(title):
            label = BodyLabel(title, role='section')
            layout.addSpacing(6)
            layout.addWidget(label)
            return label

        def text_label():
            label = BodyLabel('')
            label.setTextFormat(Qt.RichText)
            label.setWordWrap(True)
            label.setTextInteractionFlags(Qt.TextSelectableByMouse | Qt.LinksAccessibleByMouse)
            layout.addWidget(label)
            return label

        section('读屏')
        self.reads_label = text_label()
        self.more_label = text_label()
        self.more_label.setWordWrap(False)
        self.more_label.linkActivated.connect(lambda _: self.set_lanes(True))
        section(f'前后 {NOW_LOG_WINDOW:g} 秒日志')
        self.logs_label = text_label()
        section('接下来')
        self.next_label = text_label()
        self.crop_title = section('读屏原图')
        self.crop_view = CropView()
        layout.addWidget(self.crop_view)
        self.crop_text = BodyLabel('', role='secondary')
        self.crop_text.setWordWrap(True)
        self.crop_text.setTextInteractionFlags(Qt.TextSelectableByMouse)
        layout.addWidget(self.crop_text)
        layout.addStretch(1)
        scroll.setWidget(body)
        outer.addWidget(scroll, 1)

        buttons = QHBoxLayout()
        buttons.setContentsMargins(14, 6, 14, 10)
        self.events_button = PushButton('事件表', size='small')
        self.events_button.setToolTip('在下面展开事件表(能过滤)和分圈对比')
        self.events_button.clicked.connect(lambda: self.set_drawer(not self.drawer_on))
        self.lanes_button = PushButton('全部泳道', size='small')
        self.lanes_button.setToolTip('时间线画全: 出招、鼠标单独一条、每一处读屏、全部日志')
        self.lanes_button.clicked.connect(lambda: self.set_lanes(not self.lanes_on))
        for button in (self.events_button, self.lanes_button):
            button.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
            buttons.addWidget(button)
        outer.addLayout(buttons)
        self._clear_crop()

    def set_drawer(self, on):
        self.drawer_on = on
        self.events_button.set_variant('tonal' if on else 'secondary')
        self.drawerToggled.emit(on)

    def set_lanes(self, on):
        self.lanes_on = on
        self.lanes_button.set_variant('tonal' if on else 'secondary')
        self.lanesToggled.emit(on)

    def set_run(self, run, media, moments):
        self.run, self.media = run, media
        self.moments = moments
        self._moment_ts = [m[0] for m in moments]
        self._read_starts = [[e['t'] for e in row.events] for row in run.reads] if run is not None else []
        self._log_ts = [e['t'] for e in run.logs] if run is not None else []
        if media is not None and media.crops:
            self._clear_crop('点时间线上的读屏或打点、或者事件表里的读屏行, 这里显示读的那块原图(不缩)。')
        else:
            self._clear_crop()
        self.show_time(0.0)

    def show_time(self, t):
        if self.run is None:
            self.time_label.setText('')
            for label in (self.reads_label, self.more_label, self.logs_label, self.next_label):
                label.setText('')
            return
        self.time_label.setText(f'{t:.2f}s')
        self._show_reads(t)
        self._show_logs(t)
        self._show_next(t)

    def _colors(self):
        return (theme.color('text_tertiary').name(), theme.color('warning').name(), theme.color('success').name())

    def _show_reads(self, t):
        dim, warn, ok = self._colors()
        if not self.run.reads:
            self.reads_label.setText(f'<span style="color:{dim}">这局没记读屏(设置里「记录读屏」关了, 或者手打的局)</span>')
            self.more_label.setText('')
            return
        active = []
        for row, starts in zip(self.run.reads, self._read_starts):
            i = bisect.bisect_right(starts, t + BOX_WINDOW) - 1
            if i >= 0:
                event = row.events[i]
                if event.get('t2', event['t']) >= t - BOX_WINDOW:
                    active.append(event)
        rows = []
        for event in active[:NOW_READS]:
            kind = event.get('k')
            name = f'<span style="color:{dim}">{html.escape(str(READ_KINDS.get(kind, kind)))} · </span>' \
                   f"{html.escape(str(event.get('name')))}"
            if kind in ('find', 'feat'):
                value = (f'<span style="color:{ok}">认到</span>' if event.get('ok')
                         else f'<span style="color:{warn}">没认到</span>')
            else:
                value = html.escape(_num_text(event.get('v')))
            length = event.get('t2', event['t']) - event['t']
            if length >= 0.3:
                value += f' <span style="color:{dim}">· {length:.1f}s</span>'
            rows.append(f'<tr><td>{name}</td><td align="right">{value}</td></tr>')
        if rows:
            self.reads_label.setText('<table width="100%" cellspacing="0" cellpadding="1">' + ''.join(rows) + '</table>')
        else:
            self.reads_label.setText(f'<span style="color:{dim}">这一刻没读屏</span>')
        rest = len(self.run.reads) - min(len(active), NOW_READS)
        hidden = len(active) - NOW_READS
        text = f'还有 {hidden} 处也在读 · ' if hidden > 0 else (f'另 {rest} 处这一刻没读 · ' if rest else '')
        link = theme.color('accent').name()
        self.more_label.setText(f'<a href="lanes" style="color:{link}; text-decoration:none">{text}看全部泳道 ›</a>'
                                if not self.lanes_on else '')

    def _show_logs(self, t):
        dim, warn, _ = self._colors()
        lo = bisect.bisect_left(self._log_ts, t - NOW_LOG_WINDOW)
        hi = bisect.bisect_right(self._log_ts, t + NOW_LOG_WINDOW)
        # 同一句连着刷的合成一条 ×N
        groups = []
        for event in self.run.logs[lo:hi]:
            key = (event.get('l'), event.get('m'))
            if groups and groups[-1][1] == key:
                groups[-1][2] += 1
            else:
                groups.append([event, key, 1])
        if len(groups) > NOW_LOGS:
            groups = sorted(sorted(groups, key=lambda g: abs(g[0]['t'] - t))[:NOW_LOGS], key=lambda g: g[0]['t'])
        rows = []
        for event, _, count in groups:
            level = event.get('l') or 0
            tag = f'<b style="color:{warn}">{LOG_LEVELS.get(level, level)}</b> ' if level >= 30 else ''
            times = f' <span style="color:{dim}">×{count}</span>' if count > 1 else ''
            rows.append(f'<tr><td style="color:{dim}">{event["t"]:.2f}&nbsp;</td>'
                        f"<td>{tag}{html.escape(_short(event.get('m', ''), 70))}{times}</td></tr>")
        self.logs_label.setText('<table cellspacing="0" cellpadding="1">' + ''.join(rows) + '</table>' if rows else
                                f'<span style="color:{dim}">前后 {NOW_LOG_WINDOW:g} 秒没有日志</span>')

    def _show_next(self, t):
        dim = self._colors()[0]
        i = bisect.bisect_right(self._moment_ts, t + 0.0005)
        upcoming = self.moments[i:i + NOW_NEXT]
        rows = [f'<tr><td style="color:{dim}">{mt:.2f}&nbsp;</td><td>{text}</td></tr>' for mt, text in upcoming]
        self.next_label.setText('<table cellspacing="0" cellpadding="1">' + ''.join(rows) + '</table>' if rows else
                                f'<span style="color:{dim}">后面没有了</span>')

    def _clear_crop(self, text=''):
        self.crop_view.set_image(None)
        self.crop_view.setVisible(False)
        self.crop_text.setText(text)
        self.crop_text.setVisible(bool(text))
        self.crop_title.setVisible(bool(text))

    def show_event(self, event):
        if not isinstance(event, dict) or event.get('e') not in ('read', 'mark') or self.media is None:
            return
        entry, exact = self.media.crop_for(event)
        self.crop_title.setVisible(True)
        if entry is None:
            self._clear_crop(f"{event.get('name')}: 这一处没存原图(框太大、没给框、或者这局没开「存读屏那块原图」)。")
            return
        try:
            image = QImage.fromData(self.media.read(entry))
        except OSError:
            image = None
        x, y, w, h = entry.get('box') or (0, 0, 0, 0)
        text = f"{entry.get('name')}  原图 {w}×{h} @({x}, {y})  {entry['t']:.2f}s 存的"
        if 'v' in entry:
            text += f"  读数 {_num_text(entry['v'])}"
        if 'ok' in entry:
            text += '  找到' if entry['ok'] else '  没找到'
        if not exact:
            text += '\n这一段里读数没变, 显示的是之前最后一次变化时存的那张'
        self.crop_view.set_image(image)
        self.crop_view.setVisible(True)
        self.crop_text.setText(text)
        self.crop_text.setVisible(True)


class EventModel(QAbstractTableModel):
    HEADERS = ['时间(s)', '在场', '类型', '内容', '来源']

    def __init__(self):
        super().__init__()
        self.run = None
        self.rows = []
        self.events = []
        self.times = []

    def set_run(self, run):
        self.beginResetModel()
        self.run = run
        self.rows = []
        self.events = list(run.events) if run is not None else []
        if run is not None:
            for event in run.events:
                kind, text = describe(run, event)
                self.rows.append((event.get('t', 0), run.field_label_at(event.get('t', 0)), kind, text,
                                  source_text(event)))
        self.times = [row[0] for row in self.rows]
        self.endResetModel()

    def rowCount(self, parent=QModelIndex()):
        return 0 if parent.isValid() else len(self.rows)

    def columnCount(self, parent=QModelIndex()):
        return 0 if parent.isValid() else len(self.HEADERS)

    def data(self, index, role=Qt.DisplayRole):
        if not index.isValid():
            return None
        row = self.rows[index.row()]
        if role == Qt.DisplayRole:
            value = row[index.column()]
            return f'{value:.3f}' if index.column() == 0 else value
        if role == Qt.ToolTipRole and index.column() >= 3:
            return row[index.column()]
        return None

    def headerData(self, section, orientation, role=Qt.DisplayRole):
        if role == Qt.DisplayRole and orientation == Qt.Horizontal:
            return self.HEADERS[section]
        return None

    def row_near(self, t):
        if not self.times:
            return -1
        i = bisect.bisect_left(self.times, t)
        if i >= len(self.times):
            return len(self.times) - 1
        if i > 0 and t - self.times[i - 1] < self.times[i] - t:
            return i - 1
        return i


class AxisRecorderTab(QWidget):
    """C1 影院布局: 上面一排选局和操作; 中间左边画面放大当主角(左上角叠此刻信息, 下面播放条), 右边「此刻」;
    底下「进度」: 整局分圈条 + 在场/按键/提醒三条时间线。读屏泳道和事件表收着, 点「全部泳道」「事件表」再展开。"""
    # 打包/解包线程做完发回界面线程: zip 路径(解包是那一局的路径), 出错时是异常
    packed = Signal(object)
    unpacked = Signal(object)
    # 主窗口按 config.py 的 custom_tabs 建这一页时要读的两样
    add_after_default_tabs = True
    executor = None

    def __init__(self, out_dir=None):
        super().__init__()
        theme.install(self)
        # 设置在任务页的「跑轴记录」卡片里, 这页是看记录的, 换个名字分开
        self.name = '跑轴复盘'
        if FluentIcon is not None:
            self.icon = getattr(FluentIcon, 'HISTORY', FluentIcon.APPLICATION)
        else:
            self.icon = 'history'
        self._out_dir = out_dir
        self.run = None
        self.media = None
        self.summaries = []
        self.lap_info = LapInfo()
        self.moments = []
        self._moment_times = []
        self.t = 0.0
        self._listing = None
        self._packing = False
        self._unpacking = False
        self._was_recording = False
        self._refresh_due = REFRESH_TICKS
        self._last_tick = 0.0
        self.last_feedback = None
        self._diag = None
        self._compare_cache = None
        self._compare_text = ''
        self.packed.connect(self._on_packed)
        self.unpacked.connect(self._on_unpacked)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(12, 8, 12, 10)
        layout.setSpacing(6)
        # 一行: 选局(占满) / 分圈按 / 跟随最新 / 刷新 / 打包反馈 / ⋯(打开反馈包、打开文件夹、清空导出原图)
        top = QHBoxLayout()
        top.setSpacing(6)
        self.run_box = ComboBox()
        self.run_box.setMinimumWidth(280)
        self.run_box.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.run_box.currentIndexChanged.connect(self._on_run_selected)
        self.lap_box = ComboBox()
        self.lap_box.setMinimumWidth(110)
        self.lap_box.setToolTip('按哪个角色上场切圈: 整局进度条、画面左上角的第几圈、分圈对比都按这个')
        self.lap_box.currentIndexChanged.connect(self._on_lap_changed)
        self.follow = CheckBox('跟随最新')
        self.follow.setChecked(True)
        self.follow.setToolTip('打完一局自动切到最新那一局')
        refresh = PushButton('', icon='refresh')
        refresh.setToolTip('刷新记录列表')
        refresh.clicked.connect(lambda: self.refresh(force=True))
        self.pack_button = PushButton('打包反馈', variant='tonal')
        self.pack_button.clicked.connect(self._pack_feedback)
        self.more_button = PushButton('⋯')
        self.more_button.setToolTip('打开反馈包、打开文件夹、清空导出原图')
        self.more_menu = QMenu(self)
        self.import_action = self.more_menu.addAction('打开反馈包…', self._open_feedback)
        self.import_action.setToolTip('选别人发来的反馈包 zip, 解压到记录目录下的 imported 文件夹(只留最近 10 个)直接打开看,\n'
                                      '和本地记录分开放, 开新局时不会被删')
        self.folder_action = self.more_menu.addAction('打开文件夹', self._open_folder)
        self.clear_action = self.more_menu.addAction('清空导出原图', self._clear_exports)
        self.more_menu.setToolTipsVisible(True)
        self.more_button.clicked.connect(
            lambda: self.more_menu.exec(self.more_button.mapToGlobal(QPoint(0, self.more_button.height() + 2))))
        # 按钮和勾选框按自己的字宽固定, 窄了只缩下拉框
        for widget in (self.follow, refresh, self.pack_button, self.more_button):
            widget.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        top.addWidget(self.run_box, 1)
        top.addWidget(BodyLabel('分圈按'))
        for widget in (self.lap_box, self.follow, refresh, self.pack_button, self.more_button):
            top.addWidget(widget)
        layout.addLayout(top)

        # 常驻一行: 总时长、结束原因、分圈; 队伍/分辨率/按键读屏次数/各角色统计放悬停提示
        self.summary = BodyLabel('', role='secondary')
        self.summary.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Preferred)
        self.summary.setTextInteractionFlags(Qt.TextSelectableByMouse)
        layout.addWidget(self.summary)

        # 中间: 画面(主角) | 此刻
        self.frame_panel = FramePanel()
        self.frame_panel.stepped.connect(lambda t: self._set_time(t, 'step'))
        self.frame_panel.eventStep.connect(self._step_event)
        self.frame_panel.playToggled.connect(self._toggle_play)
        self.now_panel = NowPanel()
        self.now_panel.setMinimumWidth(240)
        self.now_panel.drawerToggled.connect(self._toggle_drawer)
        self.now_panel.lanesToggled.connect(self._toggle_lanes)
        stage = QSplitter(Qt.Horizontal)
        stage.setHandleWidth(10)
        stage.setStyleSheet('QSplitter::handle { background: transparent; }')  # 默认是浅色, 深色主题下一道白线
        stage.addWidget(self.frame_panel)
        stage.addWidget(self.now_panel)
        stage.setStretchFactor(0, 1)
        stage.setStretchFactor(1, 0)
        stage.setCollapsible(0, False)
        stage.setSizes([880, 300])

        # 底下「进度」: 整局一条 + 时间线
        self.progress = Card()
        progress_layout = QVBoxLayout(self.progress)
        progress_layout.setContentsMargins(0, 8, 10, 6)
        progress_layout.setSpacing(4)
        strip_row = QHBoxLayout()
        strip_row.setSpacing(0)
        whole = BodyLabel('整局', role='caption')
        whole.setFixedWidth(COMPACT_LABEL_W)
        whole.setContentsMargins(8, 0, 0, 0)
        strip_row.addWidget(whole)
        self.lap_strip = LapStrip()
        self.lap_strip.timePicked.connect(self._on_strip_picked)
        strip_row.addWidget(self.lap_strip, 1)
        progress_layout.addLayout(strip_row)
        self.scroll = ScrollArea()
        self.scroll.setWidgetResizable(False)
        self.scroll.setFrameShape(QFrame.NoFrame)
        self.scroll.setStyleSheet('QScrollArea, QScrollArea > QWidget > QWidget { background: transparent; }')
        self.canvas = TimelineCanvas(self.scroll)
        self.scroll.setWidget(self.canvas)
        self.canvas.timeClicked.connect(lambda t: self._set_time(t, 'canvas'))
        self.canvas.timeDragged.connect(lambda t: self._set_time(t, 'drag'))
        self.canvas.eventClicked.connect(self.now_panel.show_event)
        self.canvas.viewChanged.connect(self.lap_strip.set_view)
        progress_layout.addWidget(self.scroll, 1)

        # 收着的: 事件表(能过滤) / 分圈对比
        self.drawer = QWidget()
        bottom_layout = QVBoxLayout(self.drawer)
        bottom_layout.setContentsMargins(0, 0, 0, 0)
        bar = QHBoxLayout()
        self.pages = QStackedWidget()
        if SegmentedWidget is not None:
            self.switch = SegmentedWidget()
            self.switch.addItem('events', '事件', lambda: self._show_page(0))
            self.switch.addItem('laps', '分圈对比', lambda: self._show_page(1))
            self.switch.addItem('diag', '动作诊断', lambda: self._show_page(2))
            self.switch.addItem('compare', '两局对比', lambda: self._show_page(3))
            self.switch.setCurrentItem('events')
        else:
            self.switch = ComboBox()
            self.switch.addItems(['事件', '分圈对比', '动作诊断', '两局对比'])
            self.switch.currentIndexChanged.connect(self._show_page)
        self.switch.setFixedWidth(240)
        bar.addWidget(self.switch)
        self.filter = SearchLineEdit()
        self.filter.setPlaceholderText('过滤: 输入角色名、按键、模板名、函数名、日志内容…')
        bar.addWidget(self.filter, 100)
        bar.addStretch(1)  # 分圈页把过滤框藏起来时撑住, 免得切换条被拉满一整行
        bottom_layout.addLayout(bar)
        bottom_layout.addWidget(self.pages, 1)

        self.model = EventModel()
        self.proxy = QSortFilterProxyModel()
        self.proxy.setSourceModel(self.model)
        self.proxy.setFilterCaseSensitivity(Qt.CaseInsensitive)
        self.proxy.setFilterKeyColumn(-1)
        self.filter.textChanged.connect(self.proxy.setFilterFixedString)
        self.table = TableView()
        self.table.setModel(self.proxy)
        self.table.setWordWrap(False)
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SingleSelection)
        self.table.verticalHeader().setVisible(False)
        self.table.verticalHeader().setDefaultSectionSize(26)
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(QHeaderView.Interactive)
        header.setStretchLastSection(True)
        self.table.clicked.connect(self._on_row_clicked)
        self.pages.addWidget(self.table)

        lap_page = QWidget()
        lap_layout = QVBoxLayout(lap_page)
        lap_layout.setContentsMargins(0, 0, 0, 0)
        self.lap_hint = BodyLabel()
        self.lap_hint.setWordWrap(True)
        lap_layout.addWidget(self.lap_hint)
        self.lap_table = TableWidget()
        self.lap_table.setWordWrap(False)
        self.lap_table.verticalHeader().setVisible(False)
        self.lap_table.verticalHeader().setDefaultSectionSize(28)
        self.lap_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.lap_table.setSelectionMode(QAbstractItemView.SingleSelection)
        self.lap_table.cellClicked.connect(self._on_lap_cell)
        lap_layout.addWidget(self.lap_table, 1)
        self.pages.addWidget(lap_page)

        diag_page = QWidget()
        diag_layout = QVBoxLayout(diag_page)
        diag_layout.setContentsMargins(0, 0, 0, 0)
        self.diag_summary = BodyLabel()
        self.diag_summary.setWordWrap(True)
        self.diag_summary.setTextInteractionFlags(Qt.TextSelectableByMouse)
        diag_layout.addWidget(self.diag_summary)
        self.diag_table = TableWidget()
        self.diag_table.setColumnCount(4)
        self.diag_table.setHorizontalHeaderLabels(['时间(s)', '类别', '角色', '详情'])
        self.diag_table.setWordWrap(False)
        self.diag_table.verticalHeader().setVisible(False)
        self.diag_table.verticalHeader().setDefaultSectionSize(26)
        self.diag_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.diag_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.diag_table.setSelectionMode(QAbstractItemView.SingleSelection)
        diag_header = self.diag_table.horizontalHeader()
        diag_header.setSectionResizeMode(QHeaderView.Interactive)
        diag_header.setStretchLastSection(True)
        self.diag_table.cellClicked.connect(self._on_diag_cell)
        diag_layout.addWidget(self.diag_table, 1)
        self.pages.addWidget(diag_page)

        compare_page = QWidget()
        compare_layout = QVBoxLayout(compare_page)
        compare_layout.setContentsMargins(0, 0, 0, 0)
        compare_bar = QHBoxLayout()
        compare_bar.addWidget(BodyLabel('对比基准(A)'))
        self.compare_box = ComboBox()
        self.compare_box.setMinimumWidth(340)
        self.compare_box.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.compare_box.currentIndexChanged.connect(self._on_compare_selected)
        compare_bar.addWidget(self.compare_box, 1)
        self.compare_refresh = PushButton('刷新对比')
        self.compare_refresh.clicked.connect(lambda: self._update_compare(force=True))
        self.compare_copy = PushButton('复制文本')
        self.compare_copy.clicked.connect(self._copy_compare)
        for widget in (self.compare_refresh, self.compare_copy):
            widget.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
            compare_bar.addWidget(widget)
        compare_layout.addLayout(compare_bar)
        self.compare_hint = BodyLabel()
        self.compare_hint.setWordWrap(True)
        self.compare_hint.setTextInteractionFlags(Qt.TextSelectableByMouse)
        compare_layout.addWidget(self.compare_hint)
        self.compare_table = TableWidget()
        self.compare_table.setColumnCount(4)
        self.compare_table.setHorizontalHeaderLabels(['指标', 'A (基准局)', 'B (当前局)', '变化 (B-A)'])
        self.compare_table.setWordWrap(False)
        self.compare_table.verticalHeader().setVisible(False)
        self.compare_table.verticalHeader().setDefaultSectionSize(26)
        self.compare_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.compare_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.compare_table.setSelectionMode(QAbstractItemView.SingleSelection)
        compare_header = self.compare_table.horizontalHeader()
        compare_header.setSectionResizeMode(QHeaderView.Interactive)
        compare_header.setStretchLastSection(True)
        compare_layout.addWidget(self.compare_table, 1)
        self.pages.addWidget(compare_page)

        self.drawer.setVisible(False)

        self.vsplit = QSplitter(Qt.Vertical)
        self.vsplit.setHandleWidth(8)
        self.vsplit.setStyleSheet('QSplitter::handle { background: transparent; }')
        for widget in (stage, self.progress, self.drawer):
            self.vsplit.addWidget(widget)
        self.vsplit.setCollapsible(0, False)
        self.vsplit.setCollapsible(1, False)
        self.vsplit.setStretchFactor(0, 1)
        self.vsplit.setStretchFactor(1, 0)
        layout.addWidget(self.vsplit, 1)

        # 空格播放/暂停, ←/→ 上一帧/下一帧(焦点在过滤框里打字时不抢)
        for key, slot in ((Qt.Key_Space, self._toggle_play), (Qt.Key_Left, lambda: self.frame_panel.step(-1)),
                          (Qt.Key_Right, lambda: self.frame_panel.step(1))):
            shortcut = QShortcut(QKeySequence(key), self)
            shortcut.setContext(Qt.WidgetWithChildrenShortcut)
            shortcut.activated.connect(slot)

        self.play_timer = QTimer(self)
        self.play_timer.setInterval(PLAY_MS)
        self.play_timer.timeout.connect(self._play_tick)
        self.timer = QTimer(self)
        self.timer.setInterval(TICK_MS)
        self.timer.timeout.connect(self._tick)
        self.timer.start()
        self._fit_progress()
        self.refresh(force=True)

    # ---------- 数据 ----------

    @property
    def out_dir(self):
        if self._out_dir:
            return self._out_dir
        try:
            from ok.task.task import ExecutorOperation
            recorder = ExecutorOperation.__dict__.get(HOLDER_ATTR)
            if recorder is not None:
                return recorder.out_dir
        except Exception:
            pass
        return default_out_dir()

    def _tick(self):
        # 这页和轴在同一个进程里抢 GIL: 人在游戏里(coco-ww 不是前台窗口)或者正打着, 都不读盘
        recording = self._recording()
        if self._was_recording and not recording:
            self._refresh_due = 0  # 一局刚收尾, 能刷就马上刷, 别让人以为还在录
        self._was_recording = recording
        self._refresh_due -= 1
        if self._refresh_due <= 0 and not recording and self.isVisible() and self.window().isActiveWindow():
            self._refresh_due = REFRESH_TICKS
            self.refresh()

    @staticmethod
    def _recording():
        try:
            from ok.task.task import ExecutorOperation
            recorder = ExecutorOperation.__dict__.get(HOLDER_ATTR)
            return recorder is not None and recorder.run is not None
        except Exception:
            return False

    def refresh(self, force=False):
        self._update_export_button()
        run = self.run
        if run is not None and video_pending(run) and os.path.isfile(video_info_path(run.path)):
            run.video = load_video_info(run.path)  # 打完一两分钟后对时结果才写出来
            self._update_summary()
            self.frame_panel.refresh_caption()
        summaries = list_runs(self.out_dir) + list_imported_runs(self.out_dir)
        listing = [(s.path, s.finished, round(s.duration, 1)) for s in summaries]
        if not force and listing == self._listing:
            return
        newest_changed = self._listing is None or [x[0] for x in listing[:1]] != [x[0] for x in self._listing[:1]]
        self._listing = listing
        current = self.run.path if self.run is not None else None
        self.summaries = summaries
        self.run_box.blockSignals(True)
        self.run_box.clear()
        for summary in summaries:
            stamp = summary.name[:15]
            when = f'{stamp[4:6]}-{stamp[6:8]} {stamp[9:11]}:{stamp[11:13]}:{stamp[13:15]}'
            state = '' if summary.finished else '  (进行中)'
            kind = ('[导入] ' if summary.imported else '') + ('[手打] ' if summary.manual else '')
            _add_item(self.run_box, f"{when}  {kind}{' / '.join(summary.team)}  {summary.duration:.1f}s  "
                                    f"{summary.reason}{state}", summary.path)
        self.run_box.blockSignals(False)
        target = current
        if self.follow.isChecked() and summaries and (newest_changed or current is None):
            target = summaries[0].path
        index = next((i for i, s in enumerate(summaries) if s.path == target), 0 if summaries else -1)
        if index >= 0:
            self.run_box.setCurrentIndex(index)
            stale = self.run is not None and self.run.end is None and summaries[index].finished
            if force or target != current or stale:
                self.load(summaries[index].path)
        else:
            self.load(None)

    def load(self, path):
        self._stop_play()
        error = None
        self.run = None
        try:
            self.run = RunData(path) if path else None
        except (OSError, ValueError) as e:
            self.run, error = None, e
        self._diag = analyze_run(self.run) if self.run is not None else None
        self.media = None
        if self.run is not None:
            try:
                self.media = MediaIndex(path) or None
            except Exception:
                self.media = None
        self._fill_lap_box()
        self._fill_compare_box()
        self.lap_info = LapInfo(self.run, self.lap_box.currentData()) if self.run is not None else LapInfo()
        self.moments = build_moments(self.run) if self.run is not None else []
        self._moment_times = [m[0] for m in self.moments]
        self.canvas.set_run(self.run)
        self.lap_strip.set_run(self.run, self.lap_info)
        self.model.set_run(self.run)
        self.frame_panel.set_run(self.run, self.media)
        self.now_panel.set_run(self.run, self.media, self.moments)
        self._fit_progress()
        for column, width in enumerate((80, 150, 64, 520)):
            self.table.setColumnWidth(column, width)
        self._update_summary()
        if error is not None:
            self.summary.setText(f'读不了这份记录: {error}')
        self._fill_lap_table()
        self._fill_diag_page()
        if self.pages.currentIndex() == 3:
            self._update_compare()
        self._update_pack_button()
        self.t = 0.0
        if self.run is not None:
            self._set_time(0.0, 'load')

    def _fill_lap_box(self):
        self.lap_box.blockSignals(True)
        self.lap_box.clear()
        _add_item(self.lap_box, '不分圈', None)
        if self.run is not None:
            for slot in sorted(self.run.names):
                _add_item(self.lap_box, self.run.char_name(slot), slot)
            prefs = self._prefs()
            key = self._team_key()
            slot = prefs[key] if key in prefs else self.run.default_lap_slot()
            index = self.lap_box.findData(slot) if slot is not None else 0
            self.lap_box.setCurrentIndex(max(0, index))
        self.lap_box.blockSignals(False)

    def _team_key(self):
        if self.run is None:
            return ''
        return self.run.header.get('team_dir') or '__'.join(self.run.char_name(i) for i in sorted(self.run.names))

    def _prefs(self):
        try:
            with open(os.path.join(self.out_dir, PREFS_FILE), encoding='utf-8') as f:
                return json.load(f)
        except (OSError, ValueError):
            return {}

    def _save_pref(self, slot):
        prefs = self._prefs()
        prefs[self._team_key()] = slot
        self._write_prefs(prefs)

    def _write_prefs(self, prefs):
        try:
            os.makedirs(self.out_dir, exist_ok=True)
            with open(os.path.join(self.out_dir, PREFS_FILE), 'w', encoding='utf-8') as f:
                json.dump(prefs, f, ensure_ascii=False)
        except OSError:
            pass

    def _update_summary(self):
        if self.run is None:
            self.summary.setText(f'还没有记录。记录目录: {self.out_dir}')
            self.summary.setToolTip('')
            return
        self.summary.setText(headline(self.run, self.lap_box.currentData()))
        lines = list(detail_lines(self.run))
        if self._diag is not None:
            diag_lines = format_diagnostics(self.run, self._diag)
            if diag_lines:
                lines.append('')
                lines.extend(diag_lines)
        self.summary.setToolTip('\n'.join(lines))

    def _fill_diag_page(self):
        table = self.diag_table
        table.setRowCount(0)
        if self.run is None or self._diag is None:
            self.diag_summary.setText('还没有记录。')
            return
        diag = self._diag
        lines = format_diagnostics(self.run, diag)
        warn_head = f"日志告警: 警告 {diag['warns']} 条 / 报错 {diag['errors']} 条"
        if lines:
            self.diag_summary.setText(warn_head + '\n' + '\n'.join(lines))
        else:
            self.diag_summary.setText(warn_head + '\n本局未检出明显吞键、慢切人或异常。')

        items = []
        seen_sw = set()
        slow_switches = list(diag['switches']['slowest'])
        slow_switches.extend(s for s in diag['switches']['items'] if s['dur'] >= 0.7)
        slow_switches.sort(key=lambda s: s['dur'], reverse=True)
        for s in slow_switches:
            if s['t'] in seen_sw:
                continue
            seen_sw.add(s['t'])
            items.append((
                s['t'],
                '慢切人',
                f"{self.run.char_name(s['from'])}->{self.run.char_name(s['to'])}",
                f"切人耗时 {s['dur']:.2f}s (连按 {s['presses']} 次)",
                QColor(SLOW_COLOR) if s['dur'] >= 0.9 else None,
            ))
            if len(seen_sw) >= 6:
                break
        for s in diag['swallowed_skills']:
            items.append((
                s['t'],
                '疑吞技能',
                self.run.char_name(s['slot']),
                f"{s['key']} 疑被吞 ({s['why']})",
                QColor(SLOW_COLOR),
            ))
        for u in diag['unconsumed_holds']:
            items.append((
                u['t'],
                '疑吞重击',
                self.run.char_name(u['slot']),
                f"长按 {u['dur']:.2f}s 疑似未耗条 ({u['why']})",
                QColor('#E04848'),
            ))
        for e in self.run.logs:
            lvl = e.get('l') or 0
            if lvl >= 30:
                items.append((
                    e['t'],
                    '报错' if lvl >= 40 else '警告',
                    self.run.field_label_at(e['t']),
                    str(e.get('m', '')),
                    QColor('#E04848') if lvl >= 40 else QColor(SLOW_COLOR),
                ))

        items.sort(key=lambda row: row[0])
        table.setRowCount(len(items))
        for r, (t, kind, role, detail, color) in enumerate(items):
            t_item = QTableWidgetItem(f'{t:.3f}')
            t_item.setTextAlignment(Qt.AlignCenter)
            t_item.setData(Qt.UserRole, t)
            k_item = QTableWidgetItem(kind)
            k_item.setTextAlignment(Qt.AlignCenter)
            r_item = QTableWidgetItem(role)
            d_item = QTableWidgetItem(detail)
            d_item.setToolTip(detail)
            if color is not None:
                k_item.setForeground(QBrush(color))
                font = k_item.font()
                font.setBold(True)
                k_item.setFont(font)
            table.setItem(r, 0, t_item)
            table.setItem(r, 1, k_item)
            table.setItem(r, 2, r_item)
            table.setItem(r, 3, d_item)
        for col, width in enumerate((80, 90, 150, 540)):
            table.setColumnWidth(col, width)

    def _on_diag_cell(self, row, _column):
        item = self.diag_table.item(row, 0)
        t = item.data(Qt.UserRole) if item is not None else None
        if t is not None:
            self.canvas.center_on(t)
            self._set_time(t, 'row')

    def _fill_compare_box(self):
        prev_path = self.compare_box.currentData() if hasattr(self, 'compare_box') else None
        self.compare_box.blockSignals(True)
        self.compare_box.clear()
        cur_path = self.run.path if self.run is not None else None
        cur_team = list(self.run.header.get('team') or ()) if self.run is not None else []
        cur_team_names = [char_label(c) if isinstance(c, dict) else None for c in cur_team]
        candidates = [s for s in self.summaries if s.path != cur_path]
        for s in candidates:
            stamp = s.name[:15]
            when = f'{stamp[4:6]}-{stamp[6:8]} {stamp[9:11]}:{stamp[11:13]}:{stamp[13:15]}'
            _add_item(self.compare_box, f"{when}  {' / '.join(s.team)}  {s.duration:.1f}s  {s.reason}", s.path)
        if candidates:
            idx = next((i for i, s in enumerate(candidates) if s.path == prev_path), -1)
            if idx < 0 and cur_team_names:
                cur_set = {x for x in cur_team_names if x}
                idx = next((i for i, s in enumerate(candidates) if cur_set and set(s.team) == cur_set), -1)
            self.compare_box.setCurrentIndex(max(0, idx))
        self.compare_box.blockSignals(False)

    def _load_compare_run(self, path, force=False):
        if not path or not os.path.isfile(path):
            return None
        mtime = os.path.getmtime(path)
        if not force and self._compare_cache and self._compare_cache[:2] == (path, mtime):
            return self._compare_cache[2]
        rd = RunData(path)
        self._compare_cache = (path, mtime, rd)
        return rd

    def _update_compare(self, force=False):
        table = self.compare_table
        table.setRowCount(0)
        self._compare_text = ''
        if self.run is None:
            self.compare_hint.setText('当前没有打开任何记录。')
            return
        base_path = self.compare_box.currentData()
        if not base_path:
            self.compare_hint.setText('只有 1 局记录, 无法对比。再打一局或点「刷新」后即可对比。')
            return
        try:
            run_a = self._load_compare_run(base_path, force=force)
        except Exception as e:
            self.compare_hint.setText(f'读取基准局失败: {e}')
            return
        if run_a is None:
            self.compare_hint.setText('选中的基准局文件不存在。')
            return
        run_b = self.run
        slot_b = self.lap_box.currentData()
        slot_a = None
        if slot_b is not None:
            target_name = run_b.char_name(slot_b)
            slot_a = next((i for i in sorted(run_a.names) if run_a.char_name(i) == target_name), None)
        if slot_a is None:
            slot_a = run_a.default_lap_slot()
        if slot_b is None:
            slot_b = run_b.default_lap_slot()

        import statistics as _stats
        diag_a = analyze_run(run_a)
        diag_b = self._diag or analyze_run(run_b)
        laps_a = run_a.laps(slot_a) if slot_a is not None else []
        laps_b = run_b.laps(slot_b) if slot_b is not None else []
        durs_a = [d for _, d in laps_a]
        durs_b = [d for _, d in laps_b]

        ver_a = run_a.header.get('team_ver') or '-'
        ver_b = run_b.header.get('team_ver') or '-'
        self.compare_hint.setText(
            f"A(基准): {run_a.header.get('team_dir') or 'unknown'} v{ver_a} · {run_a.duration:.2f}s · {run_a.reason}\n"
            f"B(当前): {run_b.header.get('team_dir') or 'unknown'} v{ver_b} · {run_b.duration:.2f}s · {run_b.reason}"
        )
        self._compare_text = '\n'.join(compare_runs(run_a, run_b, lap_slot_a=slot_a, lap_slot_b=slot_b))

        rows = [
            ('总时长(s)', run_a.duration, run_b.duration, 'time', None),
            ('完整圈数', len(laps_a), len(laps_b), 'int', None),
            ('平均圈速(s)', (sum(durs_a) / len(durs_a)) if durs_a else None,
             (sum(durs_b) / len(durs_b)) if durs_b else None, 'time', True),
            ('中位圈速(s)', _stats.median(durs_a) if durs_a else None,
             _stats.median(durs_b) if durs_b else None, 'time', True),
            ('切人总耗时(s)', diag_a['switches']['total_s'], diag_b['switches']['total_s'], 'time', True),
            ('切人次数', diag_a['switches']['count'], diag_b['switches']['count'], 'int', None),
            ('自动F耗时(s)', diag_a['f_break']['total_s'], diag_b['f_break']['total_s'], 'time', True),
            ('疑吞技能(次)', len(diag_a['swallowed_skills']), len(diag_b['swallowed_skills']), 'int', True),
            ('疑吞重击(次)', len(diag_a['unconsumed_holds']), len(diag_b['unconsumed_holds']), 'int', True),
            ('WARN/ERROR', diag_a['warns'] + diag_a['errors'], diag_b['warns'] + diag_b['errors'], 'int', True),
        ]
        if diag_a['boss_hp'] and diag_b['boss_hp']:
            rows.append(('掉血速率(%/s)', diag_a['boss_hp']['drop_per_s'], diag_b['boss_hp']['drop_per_s'], 'time', False))

        stats_a = {s['name']: s for s in run_a.char_stats().values()}
        stats_b = {s['name']: s for s in run_b.char_stats().values()}
        char_rows = []
        for cname in list(dict.fromkeys([*stats_a, *stats_b])):
            sa = stats_a.get(cname) or {'field': 0.0, 'entries': 0}
            sb = stats_b.get(cname) or {'field': 0.0, 'entries': 0}
            va = f"{sa['field']:.1f}s / {sa['entries']}次"
            vb = f"{sb['field']:.1f}s / {sb['entries']}次"
            diff = sb['field'] - sa['field']
            char_rows.append((f'上场 · {cname}', va, vb, f'{diff:+.1f}s ({sb["entries"] - sa["entries"]:+d}次)', None))

        table.setRowCount(len(rows) + len(char_rows))
        for r, (label, va, vb, fmt, lower_better) in enumerate(rows):
            table.setItem(r, 0, QTableWidgetItem(label))
            if va is None or vb is None:
                sa_txt = '-' if va is None else (f'{va:.2f}' if fmt == 'time' else str(va))
                sb_txt = '-' if vb is None else (f'{vb:.2f}' if fmt == 'time' else str(vb))
                table.setItem(r, 1, _lap_item(sa_txt))
                table.setItem(r, 2, _lap_item(sb_txt))
                table.setItem(r, 3, _lap_item('-'))
                continue
            diff = vb - va
            if fmt == 'time':
                sa_txt, sb_txt, df_txt = f'{va:.2f}', f'{vb:.2f}', f'{diff:+.2f}'
            else:
                sa_txt, sb_txt, df_txt = str(va), str(vb), f'{diff:+d}'
            table.setItem(r, 1, _lap_item(sa_txt))
            table.setItem(r, 2, _lap_item(sb_txt))
            diff_item = _lap_item(df_txt)
            if lower_better is not None and abs(diff) > 1e-6:
                better = diff < 0 if lower_better else diff > 0
                diff_item.setForeground(QBrush(QColor('#3DB37A' if better else SLOW_COLOR)))
                font = diff_item.font()
                font.setBold(True)
                diff_item.setFont(font)
            table.setItem(r, 3, diff_item)

        offset = len(rows)
        for idx, (label, va, vb, df_txt, _) in enumerate(char_rows):
            r = offset + idx
            table.setItem(r, 0, QTableWidgetItem(label))
            table.setItem(r, 1, _lap_item(va))
            table.setItem(r, 2, _lap_item(vb))
            table.setItem(r, 3, _lap_item(df_txt))
        for col, width in enumerate((150, 140, 140, 160)):
            table.setColumnWidth(col, width)

    def _on_compare_selected(self, _index):
        if self.pages.currentIndex() == 3:
            self._update_compare()

    def _copy_compare(self):
        if not self._compare_text:
            self._update_compare()
        if not self._compare_text:
            self._toast('info', '没有可复制的对比内容', '请先选择两局记录')
            return
        cb = QApplication.clipboard()
        if cb is not None:
            cb.setText(self._compare_text)
        self._toast('success', '已复制对比文本', '可直接粘贴到聊天或文档中')

    def _fill_lap_table(self):
        table = self.lap_table
        table.clear()
        table.setRowCount(0)
        table.setColumnCount(0)
        slot = self.lap_box.currentData() if self.run is not None else None
        if slot is None:
            self.lap_hint.setText('上面「分圈按」选一个角色, 按这个角色每次上场切圈, 这里逐段对比每圈里各角色在场多久。')
            return
        columns, laps = self.run.lap_breakdown(slot)
        name = self.run.char_name(slot)
        if not laps:
            self.lap_hint.setText(f'{name} 不到两次上场, 分不了圈。')
            return
        baselines, groups = self.run.lap_baselines(columns, laps)
        main = max(groups.values(), key=len)
        mark = any(b is not None for b in baselines)
        best = self.run.default_lap_slot()
        half = best is not None and best != slot and len(self.run.entries(slot)) > len(self.run.entries(best))
        hint = f'按 {name} 上场分圈, 每格是这一段在场的秒数(含大招演出)。'
        if mark:
            hint += f'比同样上场顺序那几圈的中位数慢 {LAP_SLOW:g} 秒以上的标橙。'
        else:
            hint += '同样上场顺序的圈不到 3 圈, 不标快慢。'
        hint += '点格子, 时间线跳到那一段开头。'
        if len(groups) > 1:
            hint += f'\n这局有 {len(groups)} 种上场顺序, 各自分开比; 最下面的中位数是最常见那种({len(main)} 圈)。'
        if half:
            hint += (f'\n注意: {name} 上场 {len(self.run.entries(slot))} 次, 比 {self.run.char_name(best)}'
                     f'({len(self.run.entries(best))} 次)多, 按这个角色分出来的可能是半圈; 看整圈选 {self.run.char_name(best)}。')
        self.lap_hint.setText(hint)
        rows = [[segments.get(key) for key in columns] + [(start, total)] for start, total, segments in laps]
        medians = self.run.group_medians(columns, laps, main)
        headers = ['圈'] + [self.run.segment_label(key, columns) for key in columns] + ['整圈']
        table.setColumnCount(len(headers))
        table.setHorizontalHeaderLabels(headers)
        table.setRowCount(len(rows) + 1)
        for r, row in enumerate(rows):
            table.setItem(r, 0, _lap_item(f'第 {r + 1} 圈', row[-1][0]))
            for c, cell in enumerate(row):
                if cell is None:
                    table.setItem(r, c + 1, _lap_item('-'))
                    continue
                t0, duration = cell
                base = baselines[r][c] if baselines[r] is not None else None
                over = duration - base if base is not None else 0.0
                slow = over >= LAP_SLOW
                table.setItem(r, c + 1, _lap_item(f'{duration:.2f}' + (f'  (+{over:.1f})' if slow else ''), t0, slow))
        table.setItem(len(rows), 0, _lap_item('中位数'))
        for c, median in enumerate(medians):
            table.setItem(len(rows), c + 1, _lap_item('-' if median is None else f'{median:.2f}'))
        table.horizontalHeader().setSectionResizeMode(QHeaderView.Interactive)
        for c in range(len(headers)):
            table.setColumnWidth(c, 80 if c == 0 else 118)

    # ---------- 交互 ----------

    def _show_page(self, index):
        self.pages.setCurrentIndex(index)
        self.filter.setVisible(index == 0)
        if index == 3:
            self._update_compare()

    def _on_run_selected(self, index):
        if 0 <= index < len(self.summaries):
            self.load(self.summaries[index].path)

    def _on_lap_changed(self, _index):
        if self.run is not None:
            self._save_pref(self.lap_box.currentData())
        self.lap_info = LapInfo(self.run, self.lap_box.currentData()) if self.run is not None else LapInfo()
        self.lap_strip.set_run(self.run, self.lap_info)
        self._update_summary()
        self._fill_lap_table()
        if self.pages.currentIndex() == 3:
            self._update_compare()
        if self.run is not None:
            self.frame_panel.set_overlay(self._overlay_at(self.t))

    def _on_lap_cell(self, row, column):
        item = self.lap_table.item(row, column)
        t = item.data(Qt.UserRole) if item is not None else None
        if t is not None:
            self.canvas.center_on(t)
            self._set_time(t, 'row')

    def _on_row_clicked(self, index):
        row = self.proxy.mapToSource(index).row()
        if 0 <= row < len(self.model.rows):
            t = self.model.rows[row][0]
            self.canvas.center_on(t)
            self._set_time(t, 'row')
            self.now_panel.show_event(self.model.events[row])

    def _on_strip_picked(self, t):
        self._set_time(t, 'strip')

    # ---------- 光标 ----------

    def _set_time(self, t, source=None):
        """光标挪到 t: 时间线红线、画面、左上角信息、此刻、整局条一起跟。
        source: canvas/drag 是时间线自己挪了红线; play/step/strip/event/load 要把红线滚进视野;
        拖动、播放、点表格行时不去对表格(点行时对的话同一时刻的几行会跳来跳去)。"""
        if self.run is None:
            return
        t = max(0.0, min(self.run.duration, t))
        self.t = t
        if source not in ('canvas', 'drag'):
            self.canvas.set_cursor(t)
            if source in ('play', 'step', 'strip', 'event', 'load'):
                self.canvas.ensure_visible(t)
        self.frame_panel.show_time(t)
        self.frame_panel.set_overlay(self._overlay_at(t))
        self.now_panel.show_time(t)
        self.lap_strip.set_cursor(t)
        if source not in ('play', 'drag', 'row') and self.drawer.isVisible():
            self._sync_table(t)

    def _overlay_at(self, t):
        """画面左上角那块: 第几圈 + 时间 / 谁在场、这一段到现在多久、这一段一共多久(分了圈再给同顺序几圈的中位数) /
        最近 OPS_WINDOW 秒按了什么(E/Q/R/闪避/切人/普攻…, 连按合成 ×N) / 按住什么键、按了多久。"""
        run, info = self.run, self.lap_info
        lap = info.lap_at(t)
        title = ''
        if lap is not None:
            title = '开场' if lap < 0 else ('收尾' if lap >= len(info.laps) else f'第 {lap + 1} 圈')
        overlay = {'title': title, 'time': f'{t:.3f}s'}
        span = run.span_at(t)
        if span is not None:
            color = HIDDEN_COLOR if span.value == HUD_HIDDEN else SLOT_COLORS[span.value % len(SLOT_COLORS)]
            segment = info.segment_at(lap, t) if span.certain else None
            if segment is not None:
                t0, duration, median = segment
                text = f'本段 {t - t0:.2f}s / {duration:.2f}s' + (f' · 中位 {median:.2f}' if median is not None else '')
            else:
                text = f'本段 {t - span.t0:.2f}s / {span.t1 - span.t0:.2f}s'
            overlay['field'] = (span.label, color, text)
        if run.inputs:
            ops = []
            for label, count, last, event in run.recent_inputs(t, OPS_WINDOW, OPS_MAX):
                key = str(event.get('k') or '')
                slot = int(key) - 1 if label.startswith('切') and key.isdigit() else None
                ops.append((label + (f'×{count}' if count > 1 else ''), t - last, slot))
            overlay['ops'] = ops
        for hold in run.holds:
            if hold.t0 > t:
                break
            if t < hold.t1:
                duration = hold.t1 - hold.t0
                overlay['hold'] = (hold.label.replace('(没松)', ''), (t - hold.t0) / duration if duration else 1.0,
                                   f'{t - hold.t0:.2f}s / {duration:.2f}s')
                break
        return overlay

    def _sync_table(self, t):
        row = self.model.row_near(t)
        if row < 0:
            return
        index = self.proxy.mapFromSource(self.model.index(row, 0))
        if index.isValid():
            self.table.selectRow(index.row())
            self.table.scrollTo(index, QAbstractItemView.PositionAtCenter)

    def _step_event(self, delta):
        """跳到上/下一个事件(切人上场、按键、松开按住的键、打点)。"""
        times = self._moment_times if self.run is not None else []
        if not times:
            return
        if delta > 0:
            i = bisect.bisect_right(times, self.t + 0.0005)
            if i < len(times):
                self._set_time(times[i], 'event')
        else:
            i = bisect.bisect_left(times, self.t - 0.0005) - 1
            if i >= 0:
                self._set_time(times[i], 'event')

    # ---------- 播放 ----------

    def _toggle_play(self):
        if self.play_timer.isActive():
            self._stop_play()
            return
        if self.run is None:
            return
        if self.t >= self.run.duration - 0.01:
            self.t = 0.0
        self._last_tick = time.monotonic()
        self.play_timer.start()
        self.frame_panel.set_playing(True)

    def _stop_play(self):
        self.play_timer.stop()
        self.frame_panel.set_playing(False)

    def _play_tick(self):
        if self.run is None:
            self._stop_play()
            return
        now = time.monotonic()
        t = self.t + (now - self._last_tick) * self.frame_panel.speed
        self._last_tick = now
        if t >= self.run.duration:
            t = self.run.duration
            self._stop_play()
        self._set_time(t, 'play')

    # ---------- 展开 / 收起 ----------

    def _fit_progress(self):
        """进度区平时刚好装下三条时间线(高度固定); 全部泳道时能往上拖高。"""
        height = self.canvas.content_height() + self.scroll.horizontalScrollBar().sizeHint().height() + 2
        self.scroll.setMinimumHeight(min(height, 200) if self.canvas.full else height)
        self.scroll.setMaximumHeight(height)
        margins = self.progress.layout().contentsMargins()
        spacing = self.progress.layout().spacing()
        card = margins.top() + margins.bottom() + self.lap_strip.height() + spacing + height
        self.progress.setMaximumHeight(card)

    def _toggle_lanes(self, on):
        self.canvas.set_full(on)
        self._fit_progress()
        sizes = self.vsplit.sizes()
        total = sum(sizes)
        if on:
            want = min(self.canvas.content_height() + 60, int(total * 0.5))
        else:
            want = self.progress.maximumHeight()  # 收回三条, 空出来的高度还给画面
        sizes[0] = max(220, total - want - sizes[2])
        sizes[1] = total - sizes[0] - sizes[2]
        self.vsplit.setSizes(sizes)
        self.now_panel.show_time(self.t)  # 「看全部泳道」那行字跟着变

    def _toggle_drawer(self, on):
        self.drawer.setVisible(on)
        if on:
            sizes = self.vsplit.sizes()
            total = sum(sizes)
            sizes[2] = max(220, int(total * 0.35))
            sizes[0] = max(200, total - sizes[1] - sizes[2])
            self.vsplit.setSizes(sizes)
            self._sync_table(self.t)

    def _open_folder(self):
        # 看的是导入的反馈包就打开那个包解出来的文件夹(反馈说明、日志都在里面)
        folder = (import_root(self.run.path) if self.run is not None else None) or self.out_dir
        os.makedirs(folder, exist_ok=True)
        try:
            os.startfile(folder)
        except Exception:
            pass

    # ---------- 打开反馈包 ----------

    def _open_feedback(self):
        if self._unpacking:
            return
        from PySide6.QtWidgets import QFileDialog
        prefs = self._prefs()
        start = prefs.get('_import_dir') or os.path.join(os.path.expanduser('~'), 'Downloads')
        path, _ = QFileDialog.getOpenFileName(self, '打开反馈包', start, '反馈包 (*.zip)')
        if not path:
            return
        prefs['_import_dir'] = os.path.dirname(path)
        self._write_prefs(prefs)
        self._unpacking = True
        self.import_action.setEnabled(False)
        self.import_action.setText('解压中…')
        threading.Thread(target=self._unpack_worker, args=(path,), name='axis_recorder_import', daemon=True).start()

    def _unpack_worker(self, path):
        try:
            result = import_feedback(path, self.out_dir, busy=self._recording)
        except Exception as e:
            result = e
        try:
            self.unpacked.emit(result)
        except RuntimeError:
            pass

    def _on_unpacked(self, result):
        self._unpacking = False
        self.import_action.setEnabled(True)
        self.import_action.setText('打开反馈包…')
        if isinstance(result, Exception):
            self._toast('error', '打不开这个反馈包', str(result))
            return
        # 看别人的局时别被新打的局切走
        self.follow.setChecked(False)
        self.refresh(force=True)
        index = next((i for i, s in enumerate(self.summaries) if s.path == result), -1)
        if index >= 0:
            self.run_box.setCurrentIndex(index)
        self.load(result)

    def _update_export_button(self):
        count, size = export_usage(self.out_dir)
        text = f'清空导出原图 ({count} 次 · {size / 1e6:.0f}MB)' if count else '清空导出原图'
        if self.clear_action.text() != text:
            self.clear_action.setText(text)
        self.clear_action.setEnabled(bool(count))
        self.clear_action.setToolTip(f'F8 导出的原图在 {os.path.join(self.out_dir, EXPORT_DIR)}\n'
                                     '平时自动只留最近 20 次; 这里一次删光(正在导出的那次不动)')

    def _confirm(self, title, text):
        return bool(confirm(self, title, text))

    def _clear_exports(self):
        count, size = export_usage(self.out_dir)
        if not count or not self._confirm('清空导出原图',
                                          f'删掉 F8 导出的 {count} 次原图, 共 {size / 1e6:.0f}MB?\n'
                                          '只删导出文件夹, 每局的记录和低清画面不动。'):
            return
        clear_exports(self.out_dir)
        self._update_export_button()

    # ---------- 打包反馈 ----------

    def _update_pack_button(self):
        self.pack_button.setText('打包中…' if self._packing else '打包反馈')
        self.pack_button.setEnabled(self.run is not None and not self._packing)
        self.pack_button.setToolTip('把选中的这一局(记录、整局画面、这局 F8 导出的原图、版本、前后的 coco-ww 日志, 可选带上录屏)打成一个 zip\n'
                                    f'存在 {os.path.join(self.out_dir, FEEDBACK_DIR)}, 留最近 10 个')

    def _pack_feedback(self):
        if self.run is None or self._packing:
            return
        if self._recording():
            self._toast('warning', '正在录一局', '打完再打包, 免得跟轴抢资源')
            return
        try:
            plan = FeedbackPlan(self.run.path, self.out_dir)
        except Exception as e:
            self._toast('error', '打包失败', str(e))
            return
        accepted, note, with_exports, with_video, frames_mode = self._ask_feedback(plan)
        if not accepted:
            return
        self._packing = True
        self._update_pack_button()
        threading.Thread(target=self._pack_worker,
                         args=(plan, note, with_exports, self.lap_box.currentData(), with_video, frames_mode),
                         name='axis_recorder_feedback', daemon=True).start()

    def _ask_feedback(self, plan):
        """返回 (打不打, 哪里不对, 带不带导出原图, 带不带录屏, 整局画面怎么带)。"""
        from PySide6.QtWidgets import QButtonGroup, QRadioButton
        stamp = plan.name[:15]
        when = f'{stamp[4:6]}-{stamp[6:8]} {stamp[9:11]}:{stamp[11:13]}:{stamp[13:15]}'
        team = ' / '.join(self.run.char_name(i) for i in sorted(self.run.names))
        frames = ' + 整局画面' if plan.frames else ''
        intro = BodyLabel(f'把这一局打成一个 zip, 发给做轴的人看:\n{when} · {team} · {self.run.duration:.1f}s\n'
                          f'记录{frames} + 版本 + 这局前后的 coco-ww 日志')
        note = PlainTextEdit()
        note.setPlaceholderText('哪里不对? 比如「第 2 圈 1:05 锁暝没放 R, 站着不动」(可以不填)')
        note.setFixedHeight(110)
        widgets = [intro, note]
        modes = QButtonGroup(intro)
        if plan.frames:
            size = f'{plan.frame_width}×{plan.frame_height}' if plan.frame_width else '960×540'
            widgets.append(BodyLabel(f'整局画面 {plan.frames} 帧 · 这局按 {size} 存的'))
            row = QHBoxLayout()
            row.setContentsMargins(0, 0, 0, 0)
            row.setSpacing(14)
            choices = [(FRAMES_KEEP, f'原样 ≈{plan.frames_bytes / 1e6:.0f}MB')]
            if plan.can_standard:
                standard = plan.standard_bytes()
                choices.append((FRAMES_STANDARD, '压回标清' + (f' ≈{standard / 1e6:.0f}MB' if standard else '')))
            choices.append((FRAMES_NONE, '不带'))
            for i, (mode, text) in enumerate(choices):
                radio = QRadioButton(text)
                radio.setProperty('frames_mode', mode)
                radio.setChecked(i == 0)
                modes.addButton(radio)
                row.addWidget(radio)
            row.addStretch(1)
            holder = QWidget()
            holder.setLayout(row)
            widgets.append(holder)
            if plan.can_standard:
                hint = BodyLabel('压回标清要多花几秒; 对方要看小字、要拿去给 AI 认就选原样')
                hint.setWordWrap(True)
                widgets.append(hint)
        check = None
        if plan.exports:
            check = CheckBox(f'带上这局 F8 导出的原图({len(plan.exports)} 次 · {plan.export_images} 张 · '
                             f'{plan.export_bytes / 1e6:.0f}MB)')
            check.setChecked(True)
            widgets.append(check)
        video_check = None
        if plan.video:
            length = f' · {plan.video_duration:.0f}s' if plan.video_duration else ''
            video_check = CheckBox(f'带上录屏 {os.path.basename(plan.video)}({plan.video_bytes / 1e6:.0f}MB{length})')
            video_check.setToolTip('录屏很大, 对方要看画面细节时再带; 不带的话对方也能看到每一刻对应的录屏时间')
            widgets.append(video_check)
        total = BodyLabel()

        def frames_mode():
            checked = modes.checkedButton()
            return checked.property('frames_mode') if checked is not None else FRAMES_KEEP

        def update_total(*_):
            size = plan.total_bytes(frames_mode(), check is not None and check.isChecked(),
                                    video_check is not None and video_check.isChecked())
            total.setText(f'合计约 {size / 1e6:.1f}MB')

        modes.buttonToggled.connect(update_total)
        for toggle in (check, video_check):
            if toggle is not None:
                toggle.toggled.connect(update_total)
        update_total()
        widgets.append(total)
        if MessageBoxBase is not None:
            box = MessageBoxBase(self.window())
            box.viewLayout.addWidget(SubtitleLabel('打包反馈'))
            for widget in widgets:
                box.viewLayout.addWidget(widget)
            box.yesButton.setText('打包')
            box.cancelButton.setText('取消')
            box.widget.setMinimumWidth(520)
            accepted = bool(box.exec())
        else:
            from PySide6.QtWidgets import QDialog, QDialogButtonBox
            box = QDialog(self)
            theme.install(box)
            box.setWindowTitle('打包反馈')
            layout = QVBoxLayout(box)
            for widget in widgets:
                layout.addWidget(widget)
            buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
            buttons.button(QDialogButtonBox.Ok).setText('打包')
            buttons.button(QDialogButtonBox.Cancel).setText('取消')
            buttons.accepted.connect(box.accept)
            buttons.rejected.connect(box.reject)
            layout.addWidget(buttons)
            accepted = box.exec() == QDialog.Accepted
        return (accepted, note.toPlainText(), check is not None and check.isChecked(),
                video_check is not None and video_check.isChecked(), frames_mode())

    def _pack_worker(self, plan, note, with_exports, lap_slot, with_video=False, frames_mode=FRAMES_KEEP):
        try:
            result = build_feedback(plan, note, with_exports, lap_slot, busy=self._recording, with_video=with_video,
                                    frames_mode=frames_mode)
        except Exception as e:
            result = e
        try:
            self.packed.emit(result)
        except RuntimeError:
            pass  # 页面已经关了

    def _on_packed(self, result):
        self._packing = False
        self._update_pack_button()
        if isinstance(result, Exception):
            self._toast('error', '打包失败', str(result))
            return
        self.last_feedback = result
        size = os.path.getsize(result) if os.path.isfile(result) else 0
        self._toast('success', '反馈包打好了', f'{os.path.basename(result)}  {size / 1e6:.1f}MB, 已在文件夹里选中')
        self._reveal(result)

    def _toast(self, kind, title, text):
        tone = {'error': 'danger', 'info': 'neutral'}.get(kind, kind)
        show_toast(self, text, title, tone=tone, duration=6000)

    @staticmethod
    def _reveal(path):
        try:
            subprocess.Popen(f'explorer /select,"{os.path.normpath(path)}"')
        except Exception:
            pass

    def dispose(self):
        self.timer.stop()
        self.play_timer.stop()
