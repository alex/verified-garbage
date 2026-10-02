"""Focused regressions for benchmark selection; no builds or measurements."""

import unittest
from unittest import mock

import bench_arches as planner
import bench_compare


class Selection(unittest.TestCase):
    def setUp(self):
        planner.read.cache_clear()
        self.catalog = {'old': {'old'}, 'triple_des_ecb': {'triple_des_ecb', 'triple_des'}}

    def rows(self, paths):
        with mock.patch.object(planner, 'bench_catalog', return_value=self.catalog), \
                mock.patch.object(planner, 'registrations', return_value={'triple_des_ecb'}):
            return planner.arches(paths, base='base')

    def test_registration_addition_selects_modules_and_preserves_feature_matrix(self):
        rows = self.rows(['src/lib.rs', 'src/triple_des_ecb.rs', 'bench/benches/primitives/main.rs'])
        self.assertEqual(len(rows), 12)
        self.assertEqual({r['modules'] for r in rows}, {'triple_des triple_des_ecb'})
        for arch in planner.PLATFORMS:
            self.assertEqual([r['cpu-features'] for r in rows if r['arch'] == arch],
                             ['', *planner.CPU_FEATURES.get(arch, [])])

    def test_shared_and_unknown_dependencies_preserve_full_suite(self):
        for path in ['Cargo.lock', 'src/cpu.rs', 'src/unknown.rs']:
            with self.subTest(path=path):
                rows = self.rows([path])
                self.assertEqual(len(rows), 12)
                self.assertTrue(all(r['modules'] == '' for r in rows))

    def test_registration_edits_only(self):
        def names(lines):
            with mock.patch.object(planner.subprocess, 'check_output', return_value=lines):
                return planner.registrations('src/lib.rs', 'base')
        self.assertEqual(names('+++ b/src/lib.rs\n+pub mod triple_des_ecb;'), {'triple_des_ecb'})
        self.assertEqual(names('+#[rustfmt::skip]\n+pub(crate) mod triple_des;'), {'triple_des'})
        self.assertEqual(names('+(triple_des_ecb::USES, triple_des_ecb::bench),'), {'triple_des_ecb'})
        self.assertIsNone(planner.registrations('src/lib.rs', None))
        self.assertIsNone(names('+fn helper() {}'))
        self.assertIsNone(names('+#[cfg(feature = "alloc")]\n+pub mod old;'))

    def test_comparison_filters_each_binary_without_full_suite_fallback(self):
        with mock.patch.object(bench_compare, 'bench_catalog', return_value={'old': {'old'}}):
            self.assertEqual(bench_compare.selected_modules('base', 'old new'), 'old')
            self.assertIsNone(bench_compare.selected_modules('base', 'new'))
            self.assertEqual(bench_compare.selected_modules('base', ''), '')


if __name__ == '__main__':
    unittest.main()
