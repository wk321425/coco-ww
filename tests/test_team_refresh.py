"""海墟/过图战斗中自动换队刷新 + CharFactory 跨队隔离测试(无头模式, 不起游戏)。"""
import os
import sys
import unittest
from unittest import mock

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.char import CharFactory
from src.char.BaseChar import BaseChar, CharType
from src.task.AutoCombatTask import AutoCombatTask
from src.task.BaseCombatTask import BaseCombatTask, TeamChangedException


class _DummyMatch:
    def __init__(self, name, confidence=0.95):
        self.name = name
        self.confidence = confidence


class _FakeScene:
    def __init__(self, in_team_val=True):
        self._in_team_val = in_team_val
        self.combat = None

    def in_team(self, _fun=None):
        return self._in_team_val

    def in_combat(self):
        return None

    def set_in_combat(self):
        self.combat = True
        return True

    def set_not_in_combat(self):
        self.combat = False
        return False

    def reset_abyss_start(self):
        pass


class _DummyChar(BaseChar):
    def do_perform(self):
        pass


def _make_char(task, idx, char_name, confidence=0.98, cls=_DummyChar):
    c = cls(task, idx, char_name=char_name, confidence=confidence, char_type=CharType.MAIN_DPS)
    c.logger = mock.MagicMock()
    c.is_current_char = (idx == 0)
    return c


class CharFactoryTest(unittest.TestCase):
    def test_get_char_by_pos_replaces_sticky_low_conf_char(self):
        task = mock.MagicMock()
        old_char = BaseChar(task, 0, char_name='char_denia', confidence=0.98)

        def fake_find_one(name, box=None, threshold=0.6):
            # 模拟旧逻辑 threshold=0.6 时误中 0.65, 提高到 0.85 后不命中
            if name == 'char_denia' and threshold <= 0.65:
                return _DummyMatch('char_denia', 0.65)
            return None

        task.find_one.side_effect = fake_find_one
        task.find_best_match_in_box.side_effect = (
            lambda box, names, threshold=0.6: _DummyMatch('char_hsin', 0.95)
            if 'char_hsin' in names else None
        )

        new_char = CharFactory.get_char_by_pos(task, box='box_char_1', index=0, old_char=old_char)
        self.assertEqual(new_char.char_name, 'char_hsin')
        self.assertEqual(type(new_char).__name__, 'Hsin')

    def test_apply_team_char_classes_does_not_leak_foreign_custom_state(self):
        class ForeignCustomMornye(BaseChar):
            pass

        class NewTeamMornye(BaseChar):
            pass

        task = mock.MagicMock()
        foreign = ForeignCustomMornye(task, 2, char_name='char_moning_new', confidence=0.95)
        foreign._stale_macro_flag = True

        # 验证 builtin -> custom 继承属性, 但 foreign custom -> new custom 不继承私有属性
        builtin_hsin_cls = CharFactory.char_dict['char_hsin']['cls']
        builtin_lily_cls = CharFactory.char_dict['char_lily']['cls']
        builtin_mornye_cls = CharFactory.char_dict['char_moning_new']['cls']

        builtin_c0 = builtin_hsin_cls(task, 0, char_name='char_hsin', confidence=0.96)
        builtin_c0._preserve_me = 123
        builtin_c1 = builtin_lily_cls(task, 1, char_name='char_lily', confidence=0.96)

        with mock.patch.object(
            CharFactory,
            'load_team_char_class',
            side_effect=lambda bcls, team: NewTeamMornye if bcls is builtin_mornye_cls else bcls,
        ):
            out = CharFactory.apply_team_char_classes(task, [builtin_c0, builtin_c1, foreign])

        self.assertIs(type(out[2]), NewTeamMornye)
        self.assertFalse(hasattr(out[2], '_stale_macro_flag'))


class _TestAutoCombatTask(AutoCombatTask):
    executor = None
    frame = None


class TeamChangeDetectionTest(unittest.TestCase):
    def _make_auto_task(self, old_names=('char_denia', 'char_moning_new', 'char_qingxiao')):
        task = object.__new__(_TestAutoCombatTask)
        task.__dict__.update(
            config={
                AutoCombatTask.F_START_KEY: True,
                AutoCombatTask.F_DELAY_KEY: 0.0,
                AutoCombatTask.F_GRACE_KEY: 10.0,
                'Auto Target': False,
                'Use Liberation': True,
                'Switch to Healer before and after Combat': False,
            },
            scene=_FakeScene(in_team_val=True),
            _in_combat=True,
            _in_liberation=False,
            _in_combat_state=True,
            _abyss_force_combat_until=0.0,
            _abyss_combat_active=False,
            _abyss_timer_checked_at=0.0,
            _abyss_timer_value=None,
            _f_consumed=100.0,
            _f_grace_since=-1.0,
            _f_grace_log=0.0,
            _reset_combat_on_run=False,
            _end_seen_since=0.0,
            _team_check_at=0.0,
            _team_change_streak=0,
            _team_change_sig=None,
            _team_check_in_progress=False,
            skip_combat_check=False,
            in_sleep_check=False,
            freeze_durations=[],
            perform_watch=None,
            precise_perform=None,
            cds={},
            esc_count=0,
            can_break=False,
            boss_lv_template=None,
            boss_lv_mask=None,
            boss_lv_box=None,
            boss_health_box=None,
            boss_health=None,
            has_count_down=False,
            last_out_of_combat_time=0,
            last_in_realm_not_combat=0,
            has_lavitator=False,
            combat_start=0.0,
            out_of_combat_reason='',
            char_features_warmed_up=True,
            _app=None,
            frame=object(),
        )
        task.executor = mock.MagicMock()
        task.executor.interaction = mock.MagicMock()
        task.executor.next_frame = lambda: True
        task.chars = [_make_char(task, i, n) for i, n in enumerate(old_names)]
        task.get_box_by_name = lambda name: name
        task.in_team = lambda: (True, 0, len(task.chars))
        task.in_world = lambda: False
        task.in_team_and_world = lambda: True
        task.check_f_break = lambda: None
        task.on_combat_check = lambda: True
        task.has_target = lambda double_check=False: True
        task.load_hotkey = lambda force=False: {}
        task.load_chars = lambda: True
        task.switch_healer_enabled = lambda: False
        task.switch_healer = lambda: None
        task.log_info = lambda *a, **k: None
        return task

    def test_same_team_and_gate_guards(self):
        task = self._make_auto_task()
        # 同队 3 格都认得出旧角色 -> False
        task.find_one = lambda name, box=None, threshold=0.6: _DummyMatch(name, 0.90)
        task.find_best_match_in_box = lambda box, names, threshold=0.6: None
        self.assertFalse(task.detect_team_changed(force=True))

        # in_liberation=True 不检也不消费限频
        task._team_check_at = 0.0
        task._in_liberation = True
        self.assertFalse(task.detect_team_changed(force=False))
        self.assertEqual(task._team_check_at, 0.0)
        task._in_liberation = False

        # HUD 不在(过图中)不检也不消费限频
        task.in_team = lambda: (False, -1, 0)
        self.assertFalse(task.detect_team_changed(force=False))
        self.assertEqual(task._team_check_at, 0.0)

    def test_multi_slot_swap_penetrates_except_exception_and_resets_auto_combat(self):
        task = self._make_auto_task()
        cleanup_ran = {'ok': False}
        screen_state = {'boxes': {
            'box_char_1': 'char_denia',
            'box_char_2': 'char_moning_new',
            'box_char_3': 'char_qingxiao',
        }}
        new_team_boxes = {
            'box_char_1': 'char_hsin',
            'box_char_2': 'char_lily',
            'box_char_3': 'char_suoming',
        }

        class SwallowingMacroChar(BaseChar):
            def do_perform(self):
                prev = self.task.skip_combat_check
                self.task.skip_combat_check = True
                self.task._held().add(('key', 'w'))
                try:
                    try:
                        # 模拟跑宏期间过完海墟上半切到下半新队, 且冷却已到
                        screen_state['boxes'] = new_team_boxes
                        self.task._team_check_at = 0.0
                        # 即使 skip_combat_check=True 且包了 except Exception 也必须被打断
                        self.task.next_frame()
                    except Exception:
                        self.fail('TeamChangedException must not be caught by except Exception')
                finally:
                    cleanup_ran['ok'] = True
                    self.task.skip_combat_check = prev

        macro_char = _make_char(task, 0, 'char_denia', cls=SwallowingMacroChar)
        task.chars[0] = macro_char

        task.find_one = lambda name, box=None, threshold=0.6: (
            _DummyMatch(name, 0.90) if screen_state['boxes'].get(box) == name else None
        )
        task.find_best_match_in_box = lambda box, names, threshold=0.6: (
            _DummyMatch(screen_state['boxes'][box], 0.92) if box in screen_state['boxes'] else None
        )

        # 模拟下半刚开始玩家已经按了 F, 验证不会被错误的 drop_pending_f_press 吞掉
        task._f_consumed = 50.0
        task._f_pressed_at = 200.0

        with mock.patch('src.task.BaseWWTask.BaseWWTask.next_frame', lambda self: True), \
                mock.patch('src.task.BaseWWTask.BaseWWTask.send_key_up', lambda self, *a, **k: None), \
                mock.patch('src.task.BaseWWTask.BaseWWTask.mouse_up', lambda self, *a, **k: None), \
                mock.patch('src.task.AutoCombatTask.timer_precision.report_async'):
            ran = task.run_auto_combat()

        self.assertTrue(ran)
        self.assertTrue(cleanup_ran['ok'])
        self.assertEqual(task._held(), set())
        self.assertFalse(task._in_combat)
        self.assertFalse(task.skip_combat_check)
        self.assertEqual(task.out_of_combat_reason, 'team changed')
        self.assertEqual(task.chars, [None, None, None])
        self.assertLess(task._f_consumed, 200.0)

    def test_single_slot_swap_requires_two_confirmations(self):
        task = self._make_auto_task()
        # 仅 1 号位变成 Hsin(0.90), 2/3 号位仍是 Mornye & Qingxiao
        boxes = {
            'box_char_1': 'char_hsin',
            'box_char_2': 'char_moning_new',
            'box_char_3': 'char_qingxiao',
        }
        task.find_one = lambda name, box=None, threshold=0.6: (
            _DummyMatch(name, 0.92) if boxes.get(box) == name else None
        )
        task.find_best_match_in_box = lambda box, names, threshold=0.6: (
            _DummyMatch(boxes[box], 0.90) if box in boxes else None
        )

        with mock.patch('src.task.BaseCombatTask.time.monotonic', side_effect=[10.0, 10.30]):
            self.assertFalse(task.detect_team_changed())
            self.assertEqual(task._team_change_streak, 1)
            self.assertTrue(task.detect_team_changed())
            self.assertEqual(task._team_change_streak, 0)

    def test_unknown_slot_recovers_when_char_appears(self):
        task = self._make_auto_task(old_names=('char_hsin', 'char_suoming', 'unknown'))
        boxes = {
            'box_char_1': 'char_hsin',
            'box_char_2': 'char_suoming',
            'box_char_3': 'char_lily',
        }
        task.find_one = lambda name, box=None, threshold=0.6: (
            _DummyMatch(name, 0.95) if boxes.get(box) == name else None
        )
        task.find_best_match_in_box = lambda box, names, threshold=0.6: (
            _DummyMatch(boxes[box], 0.95) if box in boxes else None
        )
        with mock.patch('src.task.BaseWWTask.BaseWWTask.next_frame', lambda self: True), \
                mock.patch('src.task.BaseWWTask.BaseWWTask.send_key_up', lambda self, *a, **k: None), \
                mock.patch('src.task.BaseWWTask.BaseWWTask.mouse_up', lambda self, *a, **k: None), \
                mock.patch('src.task.AutoCombatTask.timer_precision.report_async'):
            self.assertTrue(task.detect_team_changed(force=True))
            ran = task.run_auto_combat()
        self.assertTrue(ran)
        self.assertEqual(task.out_of_combat_reason, 'team changed')
        self.assertEqual(task.chars, [None, None, None])


if __name__ == '__main__':
    unittest.main()
