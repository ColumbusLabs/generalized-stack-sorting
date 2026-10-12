"""Bounded regression for Proposition 5.1 of docs/classification-paper.md; not its proof."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_c_machine_equivalence import (  # noqa: E402
    contains_Sr_plus_1, generated_c_machine, generated_stack, parse_cases,
)


class CMachineEquivalenceTests(unittest.TestCase):
    def test_small_cases_agree(self):
        for r, s, max_n in ((1, 1, 6), (2, 1, 6), (2, 2, 6), (2, 3, 6), (3, 2, 6), (3, 3, 6)):
            for n in range(max_n + 1):
                self.assertEqual(generated_stack(n, r, s), generated_c_machine(n, r, s))
                self.assertEqual(generated_stack(n, r, s), generated_c_machine(n, r, s, False))

    def test_known_counts(self):
        self.assertEqual(len(generated_stack(6, 1, 1)), 132)          # Catalan
        self.assertEqual(len(generated_stack(7, 2, 3)), 4680)

    def test_container_class(self):
        self.assertTrue(contains_Sr_plus_1((1, 2, 3), 2))
        self.assertTrue(contains_Sr_plus_1((2, 1, 3), 2))
        self.assertFalse(contains_Sr_plus_1((3, 1, 2), 2))

    def test_invalid_cases(self):
        with self.assertRaises(ValueError):
            parse_cases('0,1,3')
        with self.assertRaises(ValueError):
            parse_cases('2,2,12')


if __name__ == '__main__':
    unittest.main()
