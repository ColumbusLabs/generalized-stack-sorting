"""Small regressions for the batch theorem and exact interface bound."""
from itertools import product, permutations
from pathlib import Path
import importlib.util
import unittest
from stack_sorting import three_push as normal

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    'hankel_reproducer',
    ROOT / 'evidence/three-three-enumeration/full-completion-hankel/reproduce_minors.py',
)
hankel = importlib.util.module_from_spec(spec)
spec.loader.exec_module(hankel)


def batch_matrix(state):
    row = [1, 0, 0]
    for flag in state:
        matrix = ((1, 1, 0), (1, 3, 1), (0, 4, 2 if flag == 'B' else 5))
        row = [sum(row[i] * matrix[i][j] for i in range(3)) for j in range(3)]
    return row[0]


def diagonal(state, output):
    reverse = output[::-1]
    for j, flag in enumerate(state, 1):
        height = sum(value >= j for value in reverse[:j - 1])
        if height > 2 or (flag == 'B' and height == 2 and reverse[j - 1] >= j):
            return False
    return True


def accepted(state, output):
    held = list(range(1, len(output) + 1))
    for value in output:
        index = held.index(value)
        state = normal.pop(state, index + 1)
        if state is None:
            return False
        held.pop(index)
    return state == ()


class BatchTransferTests(unittest.TestCase):
    def test_matrix_and_criterion_through_five(self):
        for size in range(1, 6):
            for word in product('BT', repeat=max(0, size - 2)):
                state = ('Z',) if size == 1 else ('Z', 'B') + word
                count = 0
                for output in permutations(range(1, size + 1)):
                    value = accepted(state, output)
                    self.assertEqual(value, diagonal(state, output), (state, output))
                    count += value
                self.assertEqual(count, batch_matrix(state), state)

    def test_exact_hankel_minors(self):
        self.assertEqual(hankel.verify()['status'], 'PASS')

    def test_one_future_token_identity(self):
        for word in product('BT', repeat=3):
            state = ('Z', 'B') + word
            self.assertEqual(hankel.candidate_count(state, 1),
                             6 * hankel.candidate_count(state, 0))

    def test_future_input_breaks_batch_criterion(self):
        state = ('Z', 'B', 'T')
        for _ in range(3):
            state = normal.pop(state, 1)
        self.assertEqual(state, ())
        for _ in range(3):
            state = normal.record(state, 1)
        self.assertEqual(state, ())
        # Identity output on six labels is legal from three held labels plus
        # three future labels, but fails the all-six-held batch criterion.
        self.assertFalse(diagonal(('Z', 'B', 'T', 'T', 'T', 'T'), tuple(range(1, 7))))


if __name__ == '__main__':
    unittest.main()
