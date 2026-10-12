"""Explicitly bounded regression for the written complete (2,3)-basis theorem.

Run from the repository root with PYTHONPATH=src. This verifies finite cases;
it does not prove the infinite classification. Uses only the standard library.
"""
import argparse
import hashlib
import json
from pathlib import Path
from time import perf_counter
from stack_sorting import basis_two_three as b
from stack_sorting import generalized as g
from stack_sorting import two_push as t


def deletion(p, i):
    v = p[i]
    return tuple(x-(x > v) for j, x in enumerate(p) if j != i)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-length', type=int, default=18,
                        help='candidate-family maximum length (6..68, default 18)')
    parser.add_argument('--raw-max-length', type=int, default=10,
                        help='original-machine maximum length (0..12, default 10)')
    parser.add_argument('--output', type=Path,
                        default=Path('evidence/two-three-basis/regression.json'))
    args = parser.parse_args()
    if not 6 <= args.max_length <= 68:
        parser.error('--max-length must be between 6 and 68')
    if not 0 <= args.raw_max_length <= 12:
        parser.error('--raw-max-length must be between 0 and 12')
    if args.raw_max_length > args.max_length:
        parser.error('--raw-max-length must not exceed --max-length')
    start = perf_counter()
    checks = raw_checks = 0
    layers = []
    for n in range(6, args.max_length+1):
        layer = b.generated_basis_at_length(n)
        assert len(layer) == b.basis_count(n)
        for p in layer:
            assert not t.recognizes_generated(p, 3)
            checks += 1
            if n <= args.raw_max_length:
                assert g.sorting_witness(g.inverse(p), 2, 3) is None
                raw_checks += 1
            for i in range(n):
                q = deletion(p, i)
                assert t.recognizes_generated(q, 3)
                checks += 1
                if n <= args.raw_max_length:
                    inv = g.inverse(q)
                    witness = g.sorting_witness(inv, 2, 3)
                    assert witness is not None
                    assert g.replay(inv, witness, 2, 3) == tuple(range(1, n))
                    raw_checks += 1
        layers.append({'n': n, 'basis_count': len(layer)})
    result = {
        'status': 'pass',
        'scope': 'finite candidate-family minimality regression, not the all-length proof',
        'orientation': 'increasing-input generated outputs; raw sorting oracle uses inverses',
        'max_length': args.max_length,
        'raw_max_length': args.raw_max_length,
        'composition_checks': checks,
        'original_machine_checks': raw_checks,
        'layers': layers,
        'duration_seconds': perf_counter()-start,
        'source_sha256': {Path(m.__file__).name: hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
                          for m in (b, g, t)},
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
