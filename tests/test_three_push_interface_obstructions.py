"""Regressions for the scalar-interface and top-query obstructions."""
from itertools import product, permutations
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest
from stack_sorting import three_push as normal

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'evidence/three-three-enumeration'


def physical(state):
    return {normal.decode(code) for code in normal.expand(state)}


def query(state, rank):
    height = normal.height(state)
    state = normal.record(state, 4)
    for k in (rank, height, height, height):
        state = normal.pop(state, k)
        if state is None:
            return None
    return state


class InterfaceObstructionTests(unittest.TestCase):
    def test_portable_rank_six_certificate(self):
        with tempfile.TemporaryDirectory() as work:
            subprocess.run([sys.executable, str(EVIDENCE / 'fixed-free-interface/check_six_row_schur.py')],
                           cwd=work, check=True, stdout=subprocess.PIPE, text=True)
            result = json.loads((Path(work) / 'independent-six-row-results.json').read_text())
        self.assertEqual(result['exact_six_by_six_determinant_leading_term'],
                         {'degree': 8, 'coefficient': 497664})
        self.assertEqual(result['schur_complement_entry_coefficients'],
                         [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 24]],
                          [[0, 0, 0, 0, 12], [0, 0, 0, 0, 48]]])

    def test_standardized_query_set_filter(self):
        for height in range(2, 5):
            for word in product('BT', repeat=height - 2):
                state = ('Z', 'B') + word
                stacks = physical(state)
                for rank in range(1, height + 1):
                    expected = {tuple(v - (v > rank) for v in s[1:])
                                for s in stacks if s[0] == rank}
                    after = query(state, rank)
                    actual = set() if after is None else physical(after)
                    self.assertEqual(actual, expected, (state, rank))

    def test_complete_physical_order_tests(self):
        initial = ('Z', 'B', 'T', 'T')
        represented = physical(initial)
        for target in permutations(range(1, 5)):
            state = initial
            held = list(range(1, 5))
            for value in target:
                state = query(state, held.index(value) + 1)
                held.remove(value)
                if state is None:
                    break
            self.assertEqual(state == (), target in represented, target)

    def test_reachable_growth_and_required_residuals(self):
        for height in range(2, 7):
            state = normal.record((), height + 1)
            self.assertEqual(len(physical(state)), 2 * 3 ** (height - 2))
        for m in range(1, 6):
            self.assertEqual(normal.pop(('Z', 'Z') + ('T',) * (m + 1), 1),
                             ('Z',) + ('O',) * m + ('B',))
            self.assertEqual(normal.pop(('Z', 'Z') + ('T',) * m + ('B',), 2),
                             ('Z', m + 1))


if __name__ == '__main__':
    unittest.main()
