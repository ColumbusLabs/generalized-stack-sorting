"""Bounded regressions for the draft unequal-width theorem, not its proof."""
from itertools import permutations
from math import factorial
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT / 'scripts'))
from stack_sorting.generalized import inverse, replay, sorting_witness
from stack_sorting.unequal_basis import (
    bounded_drop_count, delete_value, deletion_witness,
    generated_obstruction, sortable_obstruction,
)
from verify_unequal_basis import (
    StateLimitExceeded, literal_replay, normalized_generation, reverse_dual_history,
)


class UnequalBasisTests(unittest.TestCase):
    def test_explicit_three_four_examples(self):
        self.assertEqual(generated_obstruction(3, 4, 0),
                         (6, 1, 8, 2, 4, 11, 3, 5, 7, 9, 10))
        self.assertEqual(generated_obstruction(3, 4, 1),
                         (6, 1, 8, 2, 4, 10, 5, 13, 3, 7, 9, 11, 12))

    def test_permutation_and_length(self):
        for r in range(2, 8):
            for s in range(r + 1, 10):
                for m in range(6):
                    p = generated_obstruction(r, s, m)
                    self.assertEqual(len(p), 2*s + r + 2*m)
                    self.assertEqual(sorted(p), list(range(1, len(p) + 1)))

    def test_exact_specialization_to_existing_two_push_family(self):
        for s in range(3, 10):
            for m in range(8):
                maximum, n = s + 2 + 2*m, 2*s + 2 + 2*m
                old = ((s+2, 1) + tuple(range(3, s+1))
                       + tuple(v for j in range(m) for v in (s+4+2*j, s+1+2*j))
                       + (n, 2, s+1+2*m) + tuple(range(maximum+1, n)))
                self.assertEqual(generated_obstruction(2, s, m), old)

    def test_all_deletion_histories_three_replay_orientations(self):
        for r in range(2, 6):
            for s in range(r + 1, 8):
                for m in range(5):
                    p = generated_obstruction(r, s, m)
                    for d in p:
                        q = delete_value(p, d)
                        history = deletion_witness(r, s, m, d)
                        identity = tuple(range(1, len(q) + 1))
                        out, peak = literal_replay(identity, history, r, s, s+2)
                        self.assertEqual(out, q)
                        self.assertLessEqual(peak, s+2)
                        self.assertEqual(replay(inverse(q), history, r, s, s+2), identity)
                        dual = tuple(len(q)+1-v for v in reversed(q))
                        self.assertEqual(replay(dual, reverse_dual_history(history),
                                                s, r, s+2), identity)

    def test_exact_normalized_physical_orders(self):
        for r, s in ((2, 3), (3, 4), (4, 5)):
            for m in range(2):
                p = generated_obstruction(r, s, m)
                self.assertFalse(normalized_generation(p, r, s)['accepted'])
                for d in p:
                    self.assertTrue(normalized_generation(delete_value(p, d),
                                                          r, s, s+2)['accepted'])

    def test_small_unrestricted_original_machine(self):
        for r, s, m in ((2, 3, 0), (2, 3, 1), (3, 4, 0)):
            p = sortable_obstruction(r, s, m)
            self.assertIsNone(sorting_witness(p, r, s))

    def test_sorting_dual_family_formula_and_raw_rejection(self):
        p = generated_obstruction(2, 3, 0)
        self.assertEqual(sortable_obstruction(2, 3, 0), inverse(p))
        self.assertEqual(sortable_obstruction(3, 2, 0),
                         tuple(len(p)+1-v for v in reversed(p)))
        self.assertIsNone(sorting_witness(sortable_obstruction(3, 2, 0), 3, 2))

    def test_equal_width_is_not_claimed(self):
        with self.assertRaises(ValueError):
            generated_obstruction(3, 3, 1)
        with self.assertRaises(ValueError):
            sortable_obstruction(3, 3, 1)
        diagonal = (5, 1, 7, 2, 9, 4, 11, 3, 6, 8, 10)
        self.assertFalse(normalized_generation(delete_value(diagonal, 1), 3, 3)['accepted'])

    def test_low_capacity_classification_against_literal_states(self):
        for r, s in ((1, 2), (2, 1), (2, 3), (3, 2), (3, 4), (4, 3)):
            for h in range(max(r, s) + 2):
                for n in range(6):
                    count = 0
                    for p in permutations(range(1, n+1)):
                        drop = max((i-v for i, v in enumerate(p, 1)), default=-1)
                        expected = not p or (h > 0 and drop < h)
                        got = normalized_generation(inverse(p), r, s, h)['accepted']
                        self.assertEqual(got, expected)
                        count += got
                    self.assertEqual(count, bounded_drop_count(n, h))

    def test_finite_basis_patterns_at_boundary(self):
        for r, s in ((2, 3), (3, 2), (3, 4)):
            h = max(r, s) + 1
            for prefix in permutations(range(2, h+2)):
                p = prefix + (1,)
                self.assertFalse(normalized_generation(inverse(p), r, s, h)['accepted'])
                for d in p:
                    self.assertTrue(normalized_generation(inverse(delete_value(p, d)),
                                                          r, s, h)['accepted'])

    def test_count_formula_and_empty_permutation(self):
        self.assertEqual(bounded_drop_count(0, 0), 1)
        self.assertEqual(bounded_drop_count(5, 0), 0)
        self.assertEqual(bounded_drop_count(10, 1), 1)
        self.assertEqual(bounded_drop_count(7, 4), factorial(4)*4**3)
        self.assertEqual(bounded_drop_count(4, 10), factorial(4))
        self.assertTrue(normalized_generation((), 2, 3, 0)['accepted'])

    def test_invalid_parameters(self):
        for args in ((1, 3, 0), (2, 2, 0), (4, 3, 0), (2, 3, -1),
                     (True, 3, 0), (2, 3.0, 0), (2, 3, False)):
            with self.assertRaises(ValueError):
                generated_obstruction(*args)
        for d in (0, 9, True, 1.5):
            with self.assertRaises(ValueError):
                deletion_witness(2, 3, 0, d)
        for args in ((-1, 1), (1, -1), (True, 1), (1, 1.5)):
            with self.assertRaises(ValueError):
                bounded_drop_count(*args)
        with self.assertRaises(ValueError):
            delete_value((1, 1), 1)

    def test_state_limits_raise_never_approximate(self):
        with self.assertRaises(StateLimitExceeded):
            normalized_generation((3, 1, 2), 2, 3, state_limit=1)
        with self.assertRaises(ValueError):
            normalized_generation((1,), 2, 3, state_limit=0)

    def test_replayer_rejects_free_bypass_and_illegal_slots(self):
        with self.assertRaises(ValueError):
            replay((1,), (('P', 0), ('O', 0)), 2, 3, 0)
        with self.assertRaises(AssertionError):
            literal_replay((1,), (('P', 2), ('O', 0)), 2, 3, 4)
        with self.assertRaises(AssertionError):
            literal_replay((1,), (('P', 0),), 2, 3, 4)


if __name__ == '__main__':
    unittest.main()
