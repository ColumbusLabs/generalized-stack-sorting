"""Bounded exact permutation census; run with PYTHONPATH=src.

Defaults check r,s <= 4 and r+s <= 6, all input lengths through r+s+1.
No basis inference or proof is made from this finite computation.
"""
import argparse
import hashlib
import json
from itertools import permutations
from pathlib import Path
from time import perf_counter
from stack_sorting import generalized as g


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-parameter', type=int, default=4)
    parser.add_argument('--max-sum', type=int, default=6)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.max_parameter < 1 or not 2 <= args.max_sum <= 8:
        parser.error('positive parameter bound and 2 <= max-sum <= 8 required')
    start = perf_counter()
    records, tested = [], 0
    for r in range(1, args.max_parameter+1):
        for s in range(1, args.max_parameter+1):
            if r+s > args.max_sum:
                continue
            predicted = g.first_layer_patterns(r, s)
            counts = []
            for n in range(r+s+2):
                count = 0
                for p in permutations(range(1, n+1)):
                    witness = g.sorting_witness(p, r, s)
                    actual = witness is not None
                    expected = n <= r+s or p not in predicted
                    assert actual == expected, (r, s, p, actual)
                    policy = g.test_policy(p, r, s)
                    assert (policy is not None) == expected, (r, s, p, 'policy')
                    if actual:
                        target = tuple(range(1, n+1))
                        assert g.replay(p, witness, r, s) == target
                        assert g.replay(p, policy, r, s) == target
                        count += 1
                    tested += 1
                counts.append(count)
            records.append({'r_push': r, 's_pop': s, 'max_n': r+s+1,
                            'distinct_sortable_input_counts': counts,
                            'first_layer_size': len(predicted)})
    result = {'status': 'pass', 'scope': 'finite implementation checks, not proof',
              'parameters': vars(args) | {'output': None}, 'permutations_tested': tested,
              'duration_seconds': perf_counter()-start,
              'source_sha256': hashlib.sha256(Path(g.__file__).read_bytes()).hexdigest(),
              'records': records}
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
