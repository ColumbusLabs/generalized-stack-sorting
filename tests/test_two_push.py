import unittest
from itertools import permutations, product

from stack_sorting import generalized as g
from stack_sorting import two_push as t


def delete_pattern(p, i):
    value = p[i]
    return tuple(x-int(x > value) for j, x in enumerate(p) if j != i)


def raw_orders(c):
    """Independent raw top-two-push construction of the denotation."""
    result, above, height = {()}, 0, sum(c)
    for a in c:
        lower = height-above-a+1
        block = {()}
        for value in range(lower, lower+a):
            block = {p[:slot]+(value,)+p[slot:]
                     for p in block for slot in range(min(2, len(p)+1))}
        result = {p+q for p in result for q in block}
        above += a
    return result


class TwoPushTests(unittest.TestCase):
    def test_original_machine_and_capacity(self):
        for s in (2, 3, 4):
            for n in range(7):
                for p in permutations(range(1, n+1)):
                    for H in (None, 0, 2, 4):
                        exact = g.sorting_witness(p, 2, s, H) is not None
                        self.assertEqual(t.is_sortable(p, s, H), exact, (p, s, H))
                        self.assertEqual(t.recognizes_generated(g.inverse(p), s, H), exact)

    def test_every_small_composition_pop_transition(self):
        for height in range(1, 7):
            for cuts in product((0, 1), repeat=height-1):
                c, a = [], 1
                for cut in cuts:
                    if cut:
                        c.append(a)
                        a = 1
                    else:
                        a += 1
                c = tuple(c+[a])
                orders = raw_orders(c)
                for s in range(2, 6):
                    for k in range(1, height+1):
                        actual = {tuple(v-int(v > k) for v in p[:j]+p[j+1:])
                                  for p in orders for j in range(min(s, height))
                                  if p[j] == k}
                        successor = t._pop(c, k, s)
                        expected = set() if successor is None else raw_orders(successor)
                        self.assertEqual(actual, expected, (c, k, s))

    def test_uniform_family_and_all_deletions(self):
        for s in range(3, 8):
            for m in range(13):
                p = t.infinite_basis_generated(s, m)
                self.assertEqual(len(p), 2*s+2+2*m)
                self.assertEqual(sorted(p), list(range(1, len(p)+1)))
                self.assertFalse(t.recognizes_generated(p, s))
                for i in range(len(p)):
                    self.assertTrue(t.recognizes_generated(delete_pattern(p, i), s, s+2),
                                    (s, m, i))
        self.assertEqual(t.infinite_basis_sortable(3, 0), (2, 5, 3, 6, 1, 7, 8, 4))

    def test_first_family_against_original_machine(self):
        p = t.infinite_basis_sortable(3, 0)
        self.assertIsNone(g.sorting_witness(p, 2, 3))
        for i in range(len(p)):
            q = delete_pattern(p, i)
            witness = g.sorting_witness(q, 2, 3, 5)
            self.assertIsNotNone(witness)
            self.assertEqual(g.replay(q, witness, 2, 3, 5), tuple(range(1, len(q)+1)))

    def test_distinct_permutation_counts(self):
        self.assertEqual(t.permutation_counts(2, 12),
                         [1, 1, 2, 6, 24, 116, 628, 3636, 21956, 136428,
                          865700, 5583580, 36490740])
        self.assertEqual(t.permutation_counts(3, 10),
                         [1, 1, 2, 6, 24, 120, 708, 4680, 33312, 248664, 1915080])
        self.assertEqual(t.permutation_counts(4, 8), [1, 1, 2, 6, 24, 120, 720, 4992, 38544])

    def test_validation_and_resource_limit(self):
        for args in [(1, 2), (True, 2), (3, -1), (3, True)]:
            with self.assertRaises(ValueError):
                t.permutation_counts(*args)
        for s, m in [(2, 0), (3, -1), (3, True)]:
            with self.assertRaises(ValueError):
                t.infinite_basis_generated(s, m)
        for perm, s, H in [((1, 1), 3, None), ((True,), 3, None),
                           ((1,), 1, None), ((1,), 3, -1), ((1,), 3, True)]:
            with self.assertRaises(ValueError):
                t.recognizes_generated(perm, s, H)
        with self.assertRaises(RuntimeError):
            t.permutation_counts(3, 5, state_limit=1)
        self.assertTrue(t.recognizes_generated((), 3, 0))
        self.assertFalse(t.recognizes_generated((1,), 3, 0))


if __name__ == '__main__':
    unittest.main()
