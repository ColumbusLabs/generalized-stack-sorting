"""Bounded regressions; the finite-state closure proof is recorded separately."""
import json
import sys
import unittest
from functools import lru_cache
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from stack_sorting import basis_two_four as b
from stack_sorting import two_push as t
from stack_sorting.generalized import inverse


def delete(p, u):
    return tuple(v-(v > u) for v in p if v != u)


def code_of(p):
    held, code, maximum = [], [], 0
    for v in p:
        if v > maximum:
            code.append(('N', v-maximum))
            held.extend(range(maximum+1, v))
            maximum = v
        else:
            i = held.index(v)
            code.append(('H', i+1))
            held.pop(i)
    return tuple(code)


def raw_generates(p):
    """Full original physical search, allowing premature pushes."""
    n = len(p)
    @lru_cache(None)
    def visit(unread, stack, emitted):
        if emitted == n:
            return unread == n+1 and not stack
        if unread <= n:
            for slot in range(min(2, len(stack)+1)):
                if visit(unread+1, stack[:slot]+(unread,)+stack[slot:], emitted):
                    return True
        for slot in range(min(4, len(stack))):
            if stack[slot] == p[emitted]:
                if visit(unread, stack[:slot]+stack[slot+1:], emitted+1):
                    return True
        return False
    return visit(1, (), 0)


class CompleteTwoFourBasisTests(unittest.TestCase):
    def test_layer_sizes_and_orientation(self):
        for n in range(25):
            generated = b.generated_basis_at_length(n)
            self.assertEqual(len(generated), b.basis_count(n))
            self.assertEqual(len(set(generated)), len(generated))
            self.assertEqual(generated, tuple(sorted(generated)))
            self.assertEqual(len(b.generated_basis_cores_at_length(n))*48,
                             b.basis_count(n))
            self.assertEqual(b.sortable_basis_at_length(n),
                             tuple(sorted(inverse(p) for p in generated)))
            for p in generated:
                self.assertEqual(sorted(p), list(range(1, n+1)))

    def test_named_seeds_and_sharp_width(self):
        self.assertEqual(b.generated_basis_cores_at_length(7),
                         ((7, 1, 2, 3, 4, 5, 6),))
        self.assertEqual(b.generated_basis_cores_at_length(8),
                         ((6, 1, 8, 2, 3, 4, 5, 7),))
        sharp = (6, 1, 10, 5, 4, 2, 3, 7, 8, 9)
        self.assertIn(sharp, b.generated_basis_cores_at_length(10))
        self.assertEqual(1+max(v-i for i, v in enumerate(sharp, 1)), 8)

    def test_core_minimality_through_40(self):
        for n in range(7, 41):
            for p in b.generated_basis_cores_at_length(n):
                self.assertFalse(t.recognizes_generated(p, 4), p)
                for u in p:
                    self.assertTrue(t.recognizes_generated(delete(p, u), 4), (p, u))

    def test_all_orbit_minimality_through_14(self):
        for n in range(7, 15):
            for p in b.generated_basis_at_length(n):
                self.assertFalse(t.recognizes_generated(p, 4), p)
                for u in p:
                    self.assertTrue(t.recognizes_generated(delete(p, u), 4), (p, u))

    def test_raw_core_minimality_through_10(self):
        for n in range(7, 11):
            for p in b.generated_basis_cores_at_length(n):
                self.assertFalse(raw_generates(p), p)
                for u in p:
                    self.assertTrue(raw_generates(delete(p, u)), (p, u))

    def test_relay_words_match_certified_dfa_through_60(self):
        path = (Path(__file__).resolve().parents[1] / 'evidence' /
                'two-four-basis' / 'author' / 'reduced-automaton.json')
        data = json.loads(path.read_text())
        edges = {int(k): [(tuple(letter), target) for letter, target in ee]
                 for k, ee in data['min_edges'].items()}
        accepts = {int(k) for k, value in data['min_accept'].items() if value}
        current = {(data['start'], ())}
        for length in range(61):
            expected = {word for state, word in current if state in accepts}
            actual = {code_of(p)[2:-5]
                      for p in b.generated_basis_cores_at_length(length+7)
                      if p[0] == 6}
            self.assertEqual(actual, expected, length)
            current = {(target, word+(letter,)) for state, word in current
                       for letter, target in edges[state]}

    def test_argument_validation(self):
        for bad in (True, -1, 2.0, '2', None):
            for function in (b.generated_basis_cores_at_length,
                             b.generated_basis_at_length,
                             b.sortable_basis_at_length, b.basis_count):
                with self.assertRaises(ValueError):
                    function(bad)


if __name__ == '__main__':
    unittest.main()
