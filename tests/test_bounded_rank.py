import unittest
from stack_sorting import bounded_rank as tagged
from stack_sorting import three_push as normal
from stack_sorting.two_push import recognizes_generated
from stack_sorting.generalized import sorting_witness, inverse


class BoundedHeldRankTests(unittest.TestCase):
    def test_d4_distinct_permutation_coefficients(self):
        values, _ = tagged.counts_through(8, 4)
        self.assertEqual(values, [1, 1, 2, 6, 24, 120, 696, 4434, 29994])

    def test_known_one_sided_cases(self):
        self.assertEqual(tagged.counts_through(7, 1)[0], [1, 1, 2, 5, 14, 42, 132, 429])
        self.assertEqual(tagged.counts_through(7, 2)[0], [1, 1, 2, 6, 22, 90, 394, 1806])
        self.assertEqual(tagged.counts_through(7, 3)[0], [1, 1, 2, 6, 24, 114, 600, 3372])

    def test_nontrivial_width_and_intersection_witnesses(self):
        p = (6, 2, 1, 3, 4, 5)
        self.assertTrue(tagged.accepts(p, 4))
        self.assertFalse(recognizes_generated(p, 3))
        self.assertIsNone(sorting_witness(inverse(p), 3, 2))
        self.assertEqual(tagged.tokens(p), ('P',) * 5 + ('R', 3, 3, 2, 1, 0))
        self.assertFalse(tagged.accepts((7, 3, 2, 1, 4, 5, 6), 4))

    def test_long_clause_retags_without_changing_semantics(self):
        state = ('Z', 'Z', 1000, 'T', 'B')
        stack = tagged.encode(state)
        for q in (2, 0, 1, 0):
            stack = tagged.pop_offset(stack, q)
            state = normal.pop(state, normal.height(state) - q)
            self.assertIsNotNone(stack)
            self.assertEqual(tagged.decode(stack), state)
        self.assertEqual(tagged.decode(tagged.push(stack)), normal.push(state))

    def test_offset_rejection(self):
        self.assertIsNone(tagged.pop_offset((), 0))
        self.assertIsNone(tagged.pop_offset(('Z',), 1))


if __name__ == '__main__':
    unittest.main()
