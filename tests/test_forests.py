"""Independent finite checks of the mechanism-only forest encoding."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from stack_sorting.forests import forest_counts
from stack_sorting.forest_validation import run, paths, expand
from stack_sorting.patterns import OEIS


class ForestTests(unittest.TestCase):
    def test_recurrence_through_eight(self):
        values, states = forest_counts(8)
        self.assertEqual(values, list(OEIS[:9]))
        self.assertEqual(states, 552)

    def test_labeled_bijection_through_five(self):
        for row in run(5):
            self.assertEqual(row['paths'], row['distinct_permutations'])
            self.assertEqual(row['paths'], OEIS[row['n']])
            for key in ('duplicates','missing_from_forest','extra_in_forest',
                        'canonical_mismatches','replay_failures'):
                self.assertFalse(row[key], (row['n'],key))

    def test_empty_and_bypass(self):
        self.assertEqual(list(paths(0)), [((),())])
        self.assertEqual(list(paths(1)), [((1,),(('B',0),))])
        self.assertEqual(expand((('B',0),)), (('P',0),('O',0)))

    def test_bounds(self):
        for n in (-1,13,True):
            with self.subTest(n=n), self.assertRaises(ValueError):forest_counts(n)
        for n in (-1,8,True):
            with self.subTest(n=n), self.assertRaises(ValueError):run(n)
            with self.subTest(n=n), self.assertRaises(ValueError):list(paths(n))


if __name__=='__main__':
    unittest.main()
