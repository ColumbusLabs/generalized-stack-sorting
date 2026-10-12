from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
import unittest
from itertools import permutations

from stack_sorting.capacity import (
    bounded_word_counts, capacity_lower_bound, capacity_series, capacity_witness,
    history_peak, minimum_capacity,
)
from stack_sorting.model import atkinson_witness, replay
from stack_sorting.algebra import first_return_series


class CapacityTests(unittest.TestCase):
    def test_empty_and_zero_capacity(self):
        self.assertEqual(minimum_capacity(()), 0)
        self.assertEqual(capacity_witness((), 0), ())
        self.assertIsNone(capacity_witness((1,), 0))
        self.assertEqual(bounded_word_counts(0, 5), [1, 0, 0, 0, 0, 0])

    def test_bypass_needs_physical_slot(self):
        self.assertEqual(history_peak(atkinson_witness((1, 2, 3))), 1)
        self.assertEqual(bounded_word_counts(1, 8), [1]*9)
        self.assertEqual(capacity_series(1, 8), [1]*9)

    def test_minimax_and_restricted_search(self):
        for n in range(6):
            for p in permutations(range(1, n+1)):
                peak = minimum_capacity(p)
                self.assertEqual(peak, history_peak(atkinson_witness(p)))
                if peak is None:
                    continue
                self.assertEqual(peak, capacity_lower_bound(p))
                witness = capacity_witness(p, peak)
                self.assertEqual(replay(p, witness), tuple(range(1, n+1)))
                self.assertEqual(history_peak(witness), peak)
                if peak:
                    self.assertIsNone(capacity_witness(p, peak-1))

    def test_lower_bound_is_not_sortability(self):
        p = (2, 3, 4, 5, 1)
        self.assertEqual(capacity_lower_bound(p), 5)
        self.assertIsNone(minimum_capacity(p))
        self.assertIsNone(capacity_witness(p, len(p)))

    def test_two_independent_height_enumerators(self):
        for h in range(7):
            self.assertEqual(capacity_series(h, 12), bounded_word_counts(h, 12))

    def test_small_capacity_formulas(self):
        self.assertEqual(capacity_series(2, 10), [1]+[2**(n-1) for n in range(1, 11)])
        self.assertEqual(capacity_series(3, 10), [1, 1]+[2*3**(n-2) for n in range(2, 11)])
        self.assertEqual(capacity_series(4, 8), [1, 1, 2, 6, 24, 96, 380, 1500, 5916])

    def test_capacity_at_least_size(self):
        ordinary = first_return_series(10)['f']
        self.assertEqual(capacity_series(10, 10), ordinary)

    def test_input_validation(self):
        for invalid in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                capacity_witness((1,), invalid)
        with self.assertRaises(ValueError):
            minimum_capacity((1, 1))
        with self.assertRaises(ValueError):
            history_peak((('B', 0),))
        with self.assertRaises(ValueError):
            history_peak((('O', 0),))
        with self.assertRaises(ValueError):
            history_peak((('P', 0),))
        with self.assertRaises(ValueError):
            bounded_word_counts(13)
