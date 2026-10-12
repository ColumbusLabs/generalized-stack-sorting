"""Finite checks of separately reasoned quotient and first-return identities."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from stack_sorting.leaf_words import word_counts, word_histories
from stack_sorting.forests import forest_counts
from stack_sorting.forest_validation import paths
from stack_sorting.algebra import first_return_series, cubic_residual, elimination_polynomial
from stack_sorting.patterns import OEIS


class DerivationTests(unittest.TestCase):
    def test_word_forest_counts(self):
        word, states=word_counts(8)
        forest,_=forest_counts(8)
        self.assertEqual(word,forest)
        self.assertEqual(states,456)

    def test_exact_operation_language_through_five(self):
        for n in range(6):
            forest=[history for _,history in paths(n)]
            words=list(word_histories(n))
            self.assertEqual(len(words),len(set(words)))
            self.assertEqual(set(words),set(forest))

    def test_first_return_identities(self):
        series=first_return_series(12)
        self.assertEqual(series['u'],series['b'])
        self.assertEqual(series['d'],[u-f for u,f in zip(series['u'],series['f'])])
        self.assertEqual(series['f'][:len(OEIS)],list(OEIS))
        self.assertEqual(series['f'],forest_counts(12)[0])
        self.assertEqual(cubic_residual(series['f']),[0]*13)
        self.assertTrue(all(v>=0 for row in series.values() for v in row))

    def test_exact_polynomial_elimination(self):
        self.assertEqual(elimination_polynomial(),
                         {(1,3):2,(1,2):-2,(0,2):-3,(1,1):-1,(0,1):7,(0,0):-4})

    def test_bounds(self):
        for value in (-1,13,True):
            with self.assertRaises(ValueError):word_counts(value)
        for value in (-1,8,True):
            with self.assertRaises(ValueError):list(word_histories(value))
        for value in (-1,51,True):
            with self.assertRaises(ValueError):first_return_series(value)


if __name__=='__main__':unittest.main()
