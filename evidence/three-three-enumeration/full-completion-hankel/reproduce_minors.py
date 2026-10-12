#!/usr/bin/env python3
"""Recompute two exact Hankel minors from independently authored transitions.

This standard-library-only runner uses the already published independent
normal-form checker. It checks frozen exact coefficients, not fitted values.
It prints deterministic JSON and writes no files unless --output is supplied.
"""
from pathlib import Path
from functools import lru_cache
from itertools import permutations
import argparse
import importlib.util
import json
import sys

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[2]
sys.path.insert(0, str(REPO_ROOT / 'src'))
from stack_sorting import three_push as candidate

spec = importlib.util.spec_from_file_location(
    'independent_three_push',
    HERE.parent / 'normal-form-review' / 'independent_check.py',
)
independent = importlib.util.module_from_spec(spec)
spec.loader.exec_module(independent)


def record(state, count):
    height = independent.size(state)
    result = list(state)
    for _ in range(count - 1):
        result.append('Z' if height == 0 else 'B' if height == 1 else 'T')
        height += 1
    return tuple(result)


@lru_cache(None)
def independent_count(state, future):
    if not state and not future:
        return 1
    total = sum(independent_count(record(state, b), future - b)
                for b in range(1, future + 1))
    for rank in range(independent.size(state)):
        after = independent.delete_formula(state, rank)
        if after is not None:
            total += independent_count(after, future)
    return total


@lru_cache(None)
def candidate_count(state, future):
    if not state and not future:
        return 1
    total = sum(candidate_count(candidate.record(state, b), future - b)
                for b in range(1, future + 1))
    for rank in range(1, candidate.height(state) + 1):
        after = candidate.pop(state, rank)
        if after is not None:
            total += candidate_count(after, future)
    return total


def determinant(matrix, degree):
    result = [0] * (degree + 1)
    for perm in permutations(range(len(matrix))):
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(len(perm))
                           for j in range(i + 1, len(perm)))
        term = [1] + [0] * degree
        for i, j in enumerate(perm):
            other = matrix[i][j]
            term = [sum(term[k] * other[n - k] for k in range(n + 1))
                    for n in range(degree + 1)]
        result = [a + sign * b for a, b in zip(result, term)]
    return result


def modular_rank(matrix, prime=1000000007):
    matrix = [[x % prime for x in row] for row in matrix]
    rank = 0
    for col in range(len(matrix[0])):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][col], prime - 2, prime)
        matrix[rank] = [x * inverse % prime for x in matrix[rank]]
        for i in range(rank + 1, len(matrix)):
            factor = matrix[i][col]
            matrix[i] = [(x - factor * y) % prime
                         for x, y in zip(matrix[i], matrix[rank])]
        rank += 1
        if rank == len(matrix):
            break
    return rank


def verify_fixture(filename, degree, expected):
    frozen = json.loads((HERE / filename).read_text())
    rows = [tuple(w) for w in frozen['row_words']]
    cols = [tuple(w) for w in frozen['column_words']]
    matrix = [[[independent_count(('Z', 'B') + u + v, m)
                for m in range(degree + 1)] for v in cols] for u in rows]
    assert matrix == frozen['matrix_entry_coefficients']
    for i, u in enumerate(rows):
        for j, v in enumerate(cols):
            for m in range(degree + 1):
                assert matrix[i][j][m] == candidate_count(('Z', 'B') + u + v, m)
    det = determinant(matrix, degree)
    assert det == expected == frozen['determinant_coefficients']
    return matrix, {'row_words': rows, 'column_words': cols,
                    'degree_bound': degree, 'determinant_coefficients': det}


def verify():
    _, earlier = verify_fixture('earlier-minor-results.json', 4, [0, 0, 0, 0, -27648])
    matrix, later = verify_fixture('four-by-four-minor-results.json', 7,
                                  [0, 0, 0, 0, 0, 0, -76032, -3345408])
    degree = 6
    block = [[matrix[a][b][i - j] if i >= j else 0
              for j in range(degree + 1) for b in range(4)]
             for i in range(degree + 1) for a in range(4)]
    rank = modular_rank(block)
    assert rank == 22 > 3 * (degree + 1)
    return {'status': 'PASS', 'scope': 'rank at least four; no finite-rank upper bound',
            'earlier_minor': earlier, 'later_minor': later,
            'toeplitz_rank_mod_1000000007': rank, 'three_state_upper_bound': 21}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')


if __name__ == '__main__':
    main()
