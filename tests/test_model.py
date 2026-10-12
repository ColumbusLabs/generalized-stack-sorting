"""Finite model regression checks; no all-length enumeration claim."""
import unittest
from pathlib import Path
import sys
from itertools import permutations
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from stack_sorting.model import (sorting_witness, is_sortable, history_count,
    replay, inverse, generated_permutations, greedy_fixed_push, naive_counterexample, atkinson_witness)
from stack_sorting.patterns import BASIS, OEIS, avoids_basis, standardize


class ModelTests(unittest.TestCase):
    def test_empty(self):
        self.assertEqual(sorting_witness(()), ())
        self.assertEqual(history_count(()), 1)
        self.assertEqual(generated_permutations(0), {()})
        self.assertEqual(replay((), ()), ())

    def test_invalid_permutations(self):
        for function in (sorting_witness, history_count, inverse, avoids_basis):
            with self.subTest(function=function), self.assertRaises(ValueError):
                function((2, 2))

    def test_invalid_generation_size(self):
        for n in (-1, 1.0, True):
            with self.subTest(n=n), self.assertRaises(ValueError):
                generated_permutations(n)

    def test_second_slot_push_and_pop(self):
        self.assertEqual(replay((2, 1), (('P',0), ('P',1), ('O',1), ('O',0))), (1,2))

    def test_invalid_histories(self):
        cases = [(('P',1),), (('O',0),), (('P',0), ('O',1)),
                 (('P',0), ('P',0)), (('P',0),), (('X',0),),
                 (('P',2),), (('P',True),)]
        for history in cases:
            with self.subTest(history=history), self.assertRaises(ValueError):
                replay((1,), history)

    def test_exhaustive_membership_and_witness_through_six(self):
        for n in range(7):
            count = 0
            for perm in permutations(range(1, n+1)):
                witness = sorting_witness(perm)
                accepted = witness is not None
                self.assertEqual(accepted, avoids_basis(perm), perm)
                canonical = atkinson_witness(perm)
                self.assertEqual(canonical is not None, accepted, perm)
                if canonical is not None:
                    self.assertEqual(replay(perm, canonical), tuple(range(1,n+1)))
                if accepted:
                    count += 1
                    self.assertEqual(replay(perm, witness), tuple(range(1,n+1)))
            self.assertEqual(count, OEIS[n])

    def test_basis_is_rejected_and_one_deletions_accepted(self):
        for perm in BASIS:
            self.assertFalse(is_sortable(perm), perm)
            for i in range(len(perm)):
                smaller = standardize(perm[:i]+perm[i+1:])
                self.assertTrue(is_sortable(smaller), (perm, smaller))

    def test_generation_orientation_through_five(self):
        for n in range(6):
            generated = generated_permutations(n)
            sortable = {p for p in permutations(range(1,n+1)) if is_sortable(p)}
            self.assertEqual({inverse(p) for p in generated}, sortable)

    def test_inverse_is_not_identity_on_class(self):
        perm = (2,3,4,5,1)
        self.assertFalse(is_sortable(perm))
        self.assertTrue(is_sortable(inverse(perm)))
        self.assertEqual(inverse(inverse(perm)), perm)

    def test_history_counts_are_not_permutation_counts(self):
        self.assertEqual(history_count((1,2)), 3)
        self.assertEqual(history_count((2,1)), 2)
        witnesses = ((('P',0),('O',0),('P',0),('O',0)),
                     (('P',0),('P',0),('O',1),('O',0)),
                     (('P',0),('P',1),('O',0),('O',0)))
        self.assertEqual(len(set(witnesses)), 3)
        for witness in witnesses:
            self.assertEqual(replay((1,2), witness), (1,2))

    def test_minimal_fixed_push_counterexamples(self):
        for slot, expected in ((0,(2,3,4,1)), (1,(3,2,4,1))):
            self.assertEqual(naive_counterexample(slot, max_n=4), expected)
            self.assertFalse(greedy_fixed_push(expected, slot))
            self.assertTrue(is_sortable(expected))


if __name__ == '__main__':
    unittest.main()
