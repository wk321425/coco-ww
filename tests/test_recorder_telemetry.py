"""测试: 后台 HUD 遥测提取、JSONL 往返、抗噪/诊断规则、两局对比与 RecorderTab 集成。"""
import json
import os
import sys
import tempfile
import time
import unittest
from pathlib import Path

import numpy as np

os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.recorder import AxisRecorder, diagnostics, live, recorder, runs, telemetry  # noqa: E402


class TestTelemetryAndDiagnostics(unittest.TestCase):
    def test_axis_recorder_patch_points_intact(self):
        self.assertEqual(AxisRecorder._missing_patch_points(), [])

    def test_extract_hud_snapshot_synthetic_and_speed(self):
        # 1920x1080 synthetic frame (s = 0.5)
        frame = np.zeros((1080, 1920, 3), dtype=np.uint8)
        # Draw Boss HP bar (~50% width: 1180*0.5*0.5 = 295 px) in BGR (20, 100, 250)
        frame[40:52, 650:945] = (20, 100, 250)
        # Draw white forte full indicator box: x in [1126, 1156], y in [997, 1008]
        frame[997:1008, 1126:1156] = (240, 240, 240)
        # Draw E button bright white: (3185..3312)*0.5 = 1592..1656, y=(1877..1990)*0.5=938..995
        frame[945:985, 1600:1645] = (250, 250, 250)

        t0 = time.perf_counter()
        snap = telemetry.extract_hud_snapshot(frame)
        dt_ms = (time.perf_counter() - t0) * 1000.0
        self.assertIsNotNone(snap)
        self.assertLess(dt_ms, 50.0)
        self.assertIsNotNone(snap['hp'])
        self.assertAlmostEqual(snap['hp'], 0.50, delta=0.05)
        self.assertGreater(snap['f'], 0.8)
        self.assertGreater(snap['sk'][0], 0.1)
        self.assertEqual(len(snap['g']), 3)
        self.assertTrue(telemetry.hud_changed(None, snap))
        self.assertFalse(telemetry.hud_changed(snap, dict(snap), 1.0, 1.2))
        self.assertTrue(telemetry.hud_changed(snap, dict(snap), 1.0, 1.6))

    def test_boss_hp_rejects_scattered_noise_and_keeps_low_bar(self):
        # 1) Scattered red blobs separated by a large gap (e.g. Whimpering Wastes noise) -> None
        noisy = np.zeros((1080, 1920, 3), dtype=np.uint8)
        noisy[42:47, 620:625] = (20, 100, 250)
        noisy[42:47, 890:895] = (20, 100, 250)
        self.assertIsNone(telemetry.extract_boss_hp(noisy))

        # 2) Solid low HP bar (~3.5% of 590px = 21px) -> detected accurately
        low = np.zeros((1080, 1920, 3), dtype=np.uint8)
        low[42:48, 635:656] = (20, 100, 250)
        hp_low = telemetry.extract_boss_hp(low)
        self.assertIsNotNone(hp_low)
        self.assertAlmostEqual(hp_low, 21 / 590.0, delta=0.01)

        # 3) 50% bar with a small internal gap <= max_gap (9px at 1080p) -> kept intact
        gapped = np.zeros((1080, 1920, 3), dtype=np.uint8)
        gapped[42:50, 635:780] = (20, 100, 250)
        gapped[42:50, 785:930] = (20, 100, 250)
        hp_half = telemetry.extract_boss_hp(gapped)
        self.assertIsNotNone(hp_half)
        self.assertAlmostEqual(hp_half, 295 / 590.0, delta=0.02)

    def test_recorder_hud_roundtrip_and_diagnostics(self):
        with tempfile.TemporaryDirectory() as tmp:
            rec = recorder.Recorder(out_dir=tmp, plugin_version='test')
            rec._start_writer()
            run = recorder.Run(None, reads=True, logs=True)
            header = {
                'e': 'start', 'v': 1, 'wall': run.wall0, 'local': '2026-11-26 17:00:00',
                'task': 'AutoCombatTask', 'keys': {'Resonance Key': 'e', 'Echo Key': 'q', 'Liberation Key': 'r'},
                'team': [
                    {'i': 0, 'n': 'Qingxiao', 'cls': 'Qingxiao'},
                    {'i': 1, 'n': 'Denia', 'cls': 'Denia'},
                    {'i': 2, 'n': 'Mornye', 'cls': 'Mornye'},
                ],
                'size': [3840, 2160],
            }
            rec._begin(run, header)
            rec.queue.put((recorder._FIELD, run, run.t0 + 0.01, (True, 2, 3), None))
            rec.queue.put((recorder._INPUT, run, run.t0 + 0.50, 'key', 'e', 0.01, None, None))
            rec.put_hud(run, run.t0 + 0.30, {'hp': 1.00, 'g': [0.0, 0.0, 0.0], 'f': 0.50, 'sk': [0.30, 0.10, 0.20]})
            rec.put_hud(run, run.t0 + 0.70, {'hp': 0.90, 'g': [0.0, 0.0, 0.0], 'f': 0.50, 'sk': [0.30, 0.10, 0.20]})
            rec.queue.put((recorder._INPUT, run, run.t0 + 1.00, 'md', 'left', None, None, None))
            rec.put_hud(run, run.t0 + 1.05, {'hp': 0.85, 'g': [0.0, 0.0, 0.0], 'f': 0.50, 'sk': [0.30, 0.10, 0.20]})
            rec.queue.put((recorder._INPUT, run, run.t0 + 1.60, 'mu', 'left', None, None, None))
            rec.put_hud(run, run.t0 + 1.70, {'hp': 0.75, 'g': [0.8, 0.9, 0.0], 'f': 0.45, 'sk': [0.10, 0.10, 0.20]})
            rec.end_run('test_done')
            deadline = time.time() + 3.0
            while run.path is None and time.time() < deadline:
                time.sleep(0.02)
            time.sleep(0.25)
            rec.uninstall('test_cleanup')

            rd = runs.RunData(run.path)
            self.assertEqual(len(rd.huds), 4)
            self.assertEqual(runs.describe(rd, rd.huds[0])[0], '遥测')
            diag = diagnostics.analyze_run(rd)
            self.assertIsNotNone(diag['boss_hp'])
            self.assertAlmostEqual(diag['boss_hp']['total_drop'], 0.25, delta=0.01)
            self.assertEqual(len(diag['swallowed_skills']), 1)
            self.assertEqual(len(diag['unconsumed_holds']), 1)

            tail = live.RunTail(run.path)
            self.assertTrue(tail.poll())
            self.assertEqual(len(tail.data().huds), 0)

    def test_diagnostics_filters_fadeout_dips_sparse_hp_and_hidden_hud(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'fadeout_and_off_field.jsonl'
            rows = [
                {
                    'e': 'start', 'v': 1, 'wall': 1000.0, 'local': '2026-11-27 20:00:00',
                    'task': 'AutoCombatTask', 'keys': {'Resonance Key': 'e', 'Echo Key': 'q'},
                    'team': [
                        {'i': 0, 'n': 'Hsin'},
                        {'i': 1, 'n': 'Suoming'},
                        {'i': 2, 'n': 'Lily'},
                    ],
                },
                {'e': 'field', 't': 0.0, 'team': True, 'i': 2, 'cnt': 3},
                {'e': 'hud', 't': 1.0, 'hp': 0.964, 'g': [0.01, 0.04, 1.0], 'f': 0.40, 'sk': [0.30, 0.0, 0.1]},
                # Single-frame liberation fadeout V-dip: 0.964 -> 0.210 -> 0.965
                {'e': 'hud', 't': 2.0, 'hp': 0.210, 'g': [0.01, 0.04, 0.70], 'f': 0.15, 'sk': [0.0, 0.0, 0.0]},
                {'e': 'hud', 't': 3.0, 'hp': 0.965, 'g': [0.01, 0.04, 1.0], 'f': 0.40, 'sk': [0.30, 0.0, 0.1]},
                # Real burst drop + hold + boss kill & respawn (next_hp > prev_hp + 0.05 -> kept)
                {'e': 'hud', 't': 4.0, 'hp': 0.460, 'g': [0.01, 0.95, 1.0], 'f': 0.20, 'sk': [0.30, 0.0, 0.1]},
                {'e': 'hud', 't': 5.0, 'hp': 0.455, 'g': [0.01, 0.95, 1.0], 'f': 0.20, 'sk': [0.30, 0.0, 0.1]},
                {'e': 'hud', 't': 6.0, 'hp': 0.030, 'g': [0.01, 0.04, 1.0], 'f': 0.20, 'sk': [0.30, 0.0, 0.1]},
                {'e': 'hud', 't': 7.0, 'hp': 0.990, 'g': [0.01, 0.04, 1.0], 'f': 0.20, 'sk': [0.30, 0.0, 0.1]},
                # Hidden HUD pause/victory screen: high sk & glow must be ignored
                {'e': 'field', 't': 8.0, 'team': False, 'i': -1, 'cnt': 0},
                {'e': 'in', 't': 8.2, 'a': 'key', 'k': 'e', 'd': 0.05},
                {'e': 'hud', 't': 8.5, 'hp': 0.010, 'g': [0.99, 0.99, 0.99], 'f': 0.0, 'sk': [0.80, 0.80, 0.80]},
                {'e': 'end', 't': 9.0, 'reason': 'done'},
            ]
            path.write_text('\n'.join(json.dumps(r, ensure_ascii=False) for r in rows), encoding='utf-8')
            rd = runs.RunData(str(path))

            self.assertEqual(rd.off_field_glows(rd.huds[0]), [0.01, 0.04])
            self.assertLess(max(rd.off_field_glows(rd.huds[0])), 0.35)
            self.assertEqual(rd.off_field_glows(rd.huds[3]), [0.01, 0.95])
            self.assertEqual(rd.off_field_glows(rd.huds[-1]), [])
            self.assertIn('*1.00', runs.describe(rd, rd.huds[0])[1])

            diag = diagnostics.analyze_run(rd)
            self.assertIsNotNone(diag['boss_hp'])
            self.assertEqual(diag['boss_hp']['samples'], 6)
            self.assertAlmostEqual(diag['boss_hp']['total_drop'], 0.935, delta=0.005)
            self.assertEqual(diag['swallowed_skills'], [])

            # Sparse non-boss noise (<10% hp points over >=40 hud samples) -> None
            sparse_path = Path(tmp) / 'sparse_non_boss.jsonl'
            sparse_rows = [rows[0], {'e': 'field', 't': 0.0, 'team': True, 'i': 0, 'cnt': 3}]
            for idx in range(45):
                sparse_rows.append({
                    'e': 'hud', 't': 0.5 + idx * 0.5,
                    'hp': 0.04 if idx in (5, 25, 40) else None,
                    'g': [0.5, 0.0, 0.0], 'f': 0.0, 'sk': [0.0, 0.0, 0.0],
                })
            sparse_rows.append({'e': 'end', 't': 25.0, 'reason': 'done'})
            sparse_path.write_text('\n'.join(json.dumps(r, ensure_ascii=False) for r in sparse_rows), encoding='utf-8')
            diag_sparse = diagnostics.analyze_run(runs.RunData(str(sparse_path)))
            self.assertIsNone(diag_sparse['boss_hp'])


class RecorderTabIntegrationTest(unittest.TestCase):
    @staticmethod
    def _write_run(path, team_ver, dur, warn_msg=None, include_swallow=False):
        lines = [
            {'e': 'start', 'v': 1, 'wall': 1700000000.0, 'local': '2026-11-26 10:00:00',
             'task': 'AutoCombatTask', 'team_dir': 'Denia__Mornye__Qingxiao', 'team_ver': team_ver,
             'team': [
                 {'i': 0, 'n': 'Qingxiao', 'cls': 'Qingxiao'},
                 {'i': 1, 'n': 'Denia', 'cls': 'Denia'},
                 {'i': 2, 'n': 'Mornye', 'cls': 'Mornye'},
             ], 'size': [3840, 2160], 'reads': True, 'logs': True},
            {'e': 'field', 't': 0.0, 'team': True, 'i': 2, 'cnt': 3},
            {'e': 'hud', 't': 0.2, 'hp': 1.0, 'g': [0.0, 0.0, 0.0], 'f': 0.5, 'sk': [0.4, 0.2, 0.3]},
            {'e': 'in', 't': 1.0, 'a': 'key', 'k': '2'},
            {'e': 'field', 't': 1.8, 'team': True, 'i': 1, 'cnt': 3},
            {'e': 'in', 't': 2.0, 'a': 'key', 'k': 'e'},
            {'e': 'hud', 't': 2.3, 'hp': 0.85, 'g': [0.5, 0.0, 0.0], 'f': 0.5, 'sk': [0.38 if include_swallow else 0.05, 0.2, 0.3]},
            {'e': 'field', 't': 6.0, 'team': True, 'i': 0, 'cnt': 3},
            {'e': 'field', 't': 10.0, 'team': True, 'i': 2, 'cnt': 3},
        ]
        if warn_msg:
            lines.append({'e': 'log', 't': 3.5, 'l': 30, 'm': warn_msg})
        lines.append({'e': 'end', 't': dur, 'reason': 'target enemy failed', 'field_seen': dur})
        Path(path).write_text('\n'.join(json.dumps(x, ensure_ascii=False) for x in lines) + '\n', encoding='utf-8')

    def test_recorder_tab_hud_diag_and_compare(self):
        from PySide6.QtWidgets import QApplication
        from src.recorder.RecorderTab import AxisRecorderTab

        app = QApplication.instance() or QApplication([])
        self.assertIsNotNone(app)

        with tempfile.TemporaryDirectory() as tmp:
            p1 = Path(tmp, '20261126_100000_Qingxiao__Denia__Mornye.jsonl')
            p2 = Path(tmp, '20261126_101500_Qingxiao__Denia__Mornye.jsonl')
            self._write_run(p1, '1.0.4', 25.0, warn_msg='test warn old', include_swallow=True)
            self._write_run(p2, '1.0.5', 18.0, warn_msg='test warn new', include_swallow=False)

            tab = AxisRecorderTab(out_dir=tmp)
            try:
                self.assertEqual([lane.kind for lane in tab.canvas.lanes], ['field', 'keys', 'alerts'])
                tab.canvas.set_full(True)
                self.assertIn('hud', [lane.kind for lane in tab.canvas.lanes])

                self.assertGreaterEqual(tab.diag_table.rowCount(), 2)
                first_t = tab.diag_table.item(0, 0).data(0x0100)  # Qt.UserRole == 0x0100
                tab._on_diag_cell(0, 0)
                self.assertAlmostEqual(tab.t, first_t, places=3)
                self.assertAlmostEqual(tab.canvas.cursor_t, first_t, places=3)

                tab._show_page(3)
                self.assertGreaterEqual(tab.compare_table.rowCount(), 10)
                self.assertIn('总时长(s)', tab._compare_text)
                self.assertIn('Qingxiao', tab._compare_text)
            finally:
                tab.dispose()
                tab.close()


if __name__ == '__main__':
    unittest.main()
