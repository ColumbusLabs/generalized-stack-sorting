import math
import unittest
from itertools import permutations

from stack_sorting.generalized import (
    first_layer_patterns, inverse, replay, sorting_witness, test_policy,
)


class GeneralizedFirstLayerTests(unittest.TestCase):
    def test_empty_and_zero_capacity(self):
        self.assertEqual(sorting_witness((), 2, 3, 0), ())
        self.assertIsNone(sorting_witness((1,), 2, 3, 0))
        self.assertEqual(replay((), (), 2, 3, 0), ())

    def test_parameter_validation(self):
        for r, s, H in [(0, 1, None), (1, 0, None), (True, 2, None),
                        (2, 2, -1), (2, 2, False)]:
            with self.assertRaises(ValueError):
                sorting_witness((1,), r, s, H)
        for perm in [(0,), (2,), (1, 1), (True,)]:
            with self.assertRaises(ValueError):
                sorting_witness(perm, 2, 3)

    def test_replay_invalid_slots_and_capacity(self):
        for hist in [(('P', 2),), (('P', -1),), (('O', 0),), (('X', 0),),
                     (('P', False),), ()]:
            with self.assertRaises(ValueError):
                replay((1,), hist, 2, 3)
        with self.assertRaises(ValueError):
            replay((2, 1), (('P', 0), ('P', 0), ('O', 0), ('O', 0)), 2, 3, 1)

    def test_first_layer_all_small_parameters(self):
        for r, s in [(1, 1), (1, 2), (2, 1), (2, 2), (1, 3), (3, 1),
                     (2, 3), (3, 2)]:
            n = r+s+1
            predicted = first_layer_patterns(r, s)
            self.assertEqual(len(predicted), math.factorial(r)*math.factorial(s))
            for p in permutations(range(1, n+1)):
                witness = sorting_witness(p, r, s)
                self.assertEqual(witness is None, p in predicted, (r, s, p))
                self.assertEqual(test_policy(p, r, s) is None, p in predicted)
                if witness is not None:
                    self.assertEqual(replay(p, witness, r, s), tuple(range(1, n+1)))

    def test_shorter_inputs_and_sorting_dual(self):
        for p in permutations(range(1, 6)):
            dual = inverse(tuple(6-x for x in reversed(p)))
            self.assertEqual(sorting_witness(p, 2, 3) is not None,
                             sorting_witness(dual, 3, 2) is not None)
            witness = test_policy(p, 2, 3)
            self.assertIsNotNone(witness)
            self.assertEqual(replay(p, witness, 2, 3), (1, 2, 3, 4, 5))

    def test_known_greedy_failure_is_not_unsortability(self):
        p = (2, 4, 5, 1, 6, 7, 3)  # Atkinson 1998, Section 4.
        self.assertIsNone(test_policy(p, 2, 3))
        witness = sorting_witness(p, 2, 3)
        self.assertIsNotNone(witness)
        self.assertEqual(replay(p, witness, 2, 3), tuple(range(1, 8)))


if __name__ == '__main__':
    unittest.main()
