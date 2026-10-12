"""Bounded regressions; finite checks are not the all-length classification proof."""
import unittest
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from functools import lru_cache
from itertools import combinations, permutations
from stack_sorting import basis_two_three as b
from stack_sorting import two_push as t
from stack_sorting.generalized import inverse


def delete(p, i):
    v = p[i]
    return tuple(x-(x > v) for j, x in enumerate(p) if j != i)


def raw_generates(target):
    """Independent full physical search, allowing premature pushes."""
    n = len(target)
    @lru_cache(None)
    def visit(unread, stack, emitted):
        if emitted == n:
            return unread == n+1 and not stack
        if unread <= n:
            for slot in range(min(2, len(stack)+1)):
                if visit(unread+1, stack[:slot]+(unread,)+stack[slot:], emitted):
                    return True
        for slot in range(min(3, len(stack))):
            if stack[slot] == target[emitted]:
                if visit(unread, stack[:slot]+stack[slot+1:], emitted+1):
                    return True
        return False
    return visit(1, (), 0)


def contains_small_basis(p, basis):
    for k, forbidden in basis.items():
        for positions in combinations(range(len(p)), k):
            q = tuple(p[i] for i in positions)
            ranks = {v: i+1 for i, v in enumerate(sorted(q))}
            if tuple(ranks[v] for v in q) in forbidden:
                return True
    return False


class CompleteTwoThreeBasisTests(unittest.TestCase):
    def test_layer_sizes_and_orientation(self):
        for n in range(25):
            generated = b.generated_basis_at_length(n)
            self.assertEqual(len(generated), b.basis_count(n))
            self.assertEqual(len(set(generated)), len(generated))
            self.assertEqual(tuple(sorted(generated)), generated)
            self.assertEqual(b.sortable_basis_at_length(n),
                             tuple(sorted(inverse(p) for p in generated)))
            for p in generated:
                self.assertEqual(sorted(p), list(range(1, n+1)))

    def test_named_seeds(self):
        self.assertEqual(b.relay_cores(0), (
            (5, 1, 3, 8, 2, 4, 6, 7),
            (5, 1, 4, 8, 2, 3, 6, 7),
            (5, 1, 8, 4, 2, 3, 6, 7)))
        self.assertEqual(b.relay_cores(1)[2], (5, 1, 7, 4, 3, 10, 2, 6, 8, 9))

    def test_minimality_composition_through_18(self):
        for n in range(6, 19):
            for p in b.generated_basis_at_length(n):
                self.assertFalse(t.recognizes_generated(p, 3), p)
                for i in range(n):
                    self.assertTrue(t.recognizes_generated(delete(p, i), 3), (p, i))

    def test_raw_minimality_through_10(self):
        for n in range(6, 11):
            for p in b.generated_basis_at_length(n):
                self.assertFalse(raw_generates(p), p)
                for i in range(n):
                    self.assertTrue(raw_generates(delete(p, i)), (p, i))

    def test_raw_characterization_every_input_through_7(self):
        basis = {k: set(b.generated_basis_at_length(k)) for k in (6, 7)}
        for n in range(8):
            for p in permutations(range(1, n+1)):
                self.assertEqual(raw_generates(p), not contains_small_basis(p, basis), p)

    def test_argument_validation(self):
        for bad in (True, -1, 2.0, '2', None):
            for function in (b.relay_cores, b.generated_basis_at_length,
                             b.sortable_basis_at_length, b.basis_count):
                with self.assertRaises(ValueError):
                    function(bad)


if __name__ == '__main__':
    unittest.main()
