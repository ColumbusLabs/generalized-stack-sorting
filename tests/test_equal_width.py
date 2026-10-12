"""Bounded regressions for the (r,r) families; these are not their proof."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT / 'scripts'))
from stack_sorting.equal_width import (
    deletion_witness, generated_obstruction, sortable_obstruction,
)
from stack_sorting.generalized import inverse, replay
from stack_sorting.three_three import generated_obstruction as three_three
from verify_three_three import pruned_sortable


class EqualWidthTests(unittest.TestCase):
    def test_displayed_members(self):
        self.assertEqual(generated_obstruction(4, 0, 'A'),
                         (6, 1, 8, 2, 10, 3, 5, 13, 4, 15, 12, 7, 19, 16, 11, 9,
                          14, 17, 18))
        self.assertEqual(generated_obstruction(5, 0, 'A'),
                         (7, 1, 9, 2, 11, 3, 13, 4, 6, 16, 5, 18, 15, 8, 22, 19,
                          14, 10, 12, 17, 20, 21))

    def test_specializes_to_three_three(self):
        for k in range(6):
            for kind in 'AB':
                self.assertEqual(generated_obstruction(3, k, kind), three_three(kind, k))

    def test_permutations_lengths_inverse(self):
        for r in range(3, 9):
            for k in range(5):
                for kind, extra in (('A', 7), ('B', 8)):
                    p = generated_obstruction(r, k, kind)
                    self.assertEqual(sorted(p), list(range(1, 3*r + extra + 3*k + 1)))
                    self.assertEqual(sortable_obstruction(r, k, kind), inverse(p))

    def test_every_deletion_witness_replays(self):
        for r in range(3, 8):
            for k in range(3):
                for kind in 'AB':
                    p = generated_obstruction(r, k, kind)
                    n = len(p)
                    for a in p:
                        q = [v for v in p if v != a]
                        rank = {v: i + 1 for i, v in enumerate(sorted(q))}
                        self.assertEqual(
                            replay(tuple(range(1, n)), deletion_witness(r, k, kind, a), r, r),
                            tuple(rank[v] for v in q))

    def test_capacity_statistic(self):
        def w(p):
            return 1 + max(v - i for i, v in enumerate(p, 1))
        for r in range(3, 12):
            for k in range(6):
                self.assertEqual(w(generated_obstruction(r, k, 'B')), r + 2)
                self.assertEqual(w(generated_obstruction(r, k, 'A')), r + 3)

    def test_rejection_bounded(self):
        for r, k in ((3, 0), (3, 1), (4, 0), (4, 1)):
            for kind in 'AB':
                self.assertFalse(pruned_sortable(inverse(generated_obstruction(r, k, kind)), r, r))

    def test_invalid_arguments(self):
        with self.assertRaises(ValueError):
            generated_obstruction(2, 0, 'A')
        with self.assertRaises(ValueError):
            generated_obstruction(3, 0, 'C')
        with self.assertRaises(ValueError):
            deletion_witness(4, 0, 'A', 999)


if __name__ == '__main__':
    unittest.main()
