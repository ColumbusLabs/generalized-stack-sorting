"""Bounded regressions for the (3,3) families; these are not their proof."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT / 'scripts'))
from stack_sorting.generalized import inverse, replay, sorting_witness
from stack_sorting.three_three import (
    deletion_witness, generated_obstruction, sortable_obstruction,
)
from verify_three_three import pruned_sortable


class ThreeThreeTests(unittest.TestCase):
    def test_displayed_members(self):
        self.assertEqual(generated_obstruction('A', 0),
                         (5, 1, 7, 2, 4, 10, 3, 12, 9, 6, 16, 13, 8, 11, 14, 15))
        self.assertEqual(generated_obstruction('B', 1),
                         (5, 1, 7, 2, 4, 10, 3, 12, 9, 6, 15, 13, 11, 18, 16, 20,
                          8, 14, 17, 19))

    def test_permutations_and_lengths(self):
        for k in range(8):
            for name, base in (('A', 16), ('B', 17)):
                p = generated_obstruction(name, k)
                self.assertEqual(sorted(p), list(range(1, base + 3*k + 1)))
                self.assertEqual(sortable_obstruction(name, k), inverse(p))

    def test_rejection_bounded(self):
        for k in range(3):
            for name in 'AB':
                self.assertFalse(pruned_sortable(inverse(generated_obstruction(name, k))))

    def test_every_deletion_witness_replays(self):
        for k in range(4):
            for name in 'AB':
                p = generated_obstruction(name, k)
                n = len(p)
                for a in p:
                    ops = deletion_witness(name, k, a)
                    q = [v for v in p if v != a]
                    rank = {v: i + 1 for i, v in enumerate(sorted(q))}
                    self.assertEqual(replay(tuple(range(1, n)), ops, 3, 3),
                                     tuple(rank[v] for v in q))

    def test_pruned_search_matches_unpruned_on_small_inputs(self):
        import random
        rng = random.Random(33)
        for n in range(1, 9):
            for _ in range(40):
                pi = list(range(1, n + 1))
                rng.shuffle(pi)
                self.assertEqual(pruned_sortable(pi),
                                 sorting_witness(tuple(pi), 3, 3) is not None)

    def test_unpruned_contradiction_fails_verification(self):
        import tempfile
        from unittest import mock
        import verify_three_three as vt
        for status, code, label in (('generated', 1, 'FAILED'),
                                    ('STOPPED', 0, 'passed'),
                                    ('rejected', 0, 'passed')):
            fake = {'member': 'A(0)', 'status': status}
            with tempfile.TemporaryDirectory() as tmp, \
                    mock.patch.object(vt, 'unpruned_a0', return_value=fake), \
                    mock.patch('builtins.print'):
                out = Path(tmp) / 'v.json'
                self.assertEqual(vt.main(['--max-k', '0', '--unpruned-a0',
                                          '--output', str(out)]), code)
                import json
                self.assertEqual(json.loads(out.read_text())['status'], label)

    def test_invalid_arguments(self):
        with self.assertRaises(ValueError):
            generated_obstruction('C', 0)
        with self.assertRaises(ValueError):
            generated_obstruction('A', -1)
        with self.assertRaises(ValueError):
            deletion_witness('A', 0, 99)


if __name__ == '__main__':
    unittest.main()
