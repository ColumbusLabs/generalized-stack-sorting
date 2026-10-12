#!/usr/bin/env python3
"""Bounded, reproducible checks of the (r,r) families; these are not a proof.

Standard library only; local; no hosted CI. For 3 <= r <= --max-r and
k <= --max-k it checks, for A_r(k) and B_r(k):
- that the member is a permutation and agrees with the (3,3) module at r = 3;
- that every single-deletion witness of stack_sorting.equal_width replays,
  through the repository's unchanged generalized.replay, to the standardized
  deletion;
- the statistic w and the maximum height of each witness.
Rejection is checked separately by a pruned exhaustive search, for
r <= --reject-max-r and k <= --reject-max-k only (it grows quickly with r).
A STOPPED search carries no conclusion and makes the run FAIL only when it
returns 'generated'.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT / 'scripts'))
from stack_sorting.equal_width import (  # noqa: E402
    deletion_witness, generated_obstruction,
)
from stack_sorting.generalized import inverse, replay  # noqa: E402
from stack_sorting.three_three import generated_obstruction as three_three  # noqa: E402
from verify_three_three import pruned_sortable  # noqa: E402


def w(p):
    return 1 + max(v - i for i, v in enumerate(p, 1)) if p else 0


def height(ops):
    h = m = 0
    for kind, _ in ops:
        h += 1 if kind == 'P' else -1
        m = max(m, h)
    return m


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def check_witnesses(r, k, kind):
    p = generated_obstruction(r, k, kind)
    n = len(p)
    heights = []
    for a in p:
        ops = deletion_witness(r, k, kind, a)
        q = [v for v in p if v != a]
        rank = {v: i + 1 for i, v in enumerate(sorted(q))}
        if replay(tuple(range(1, n)), ops, r, r) != tuple(rank[v] for v in q):
            raise AssertionError(f'replay mismatch r={r} k={k} {kind} deleting {a}')
        heights.append(height(ops))
    return {'r': r, 'k': k, 'family': kind, 'length': n,
            'is_permutation': sorted(p) == list(range(1, n + 1)),
            'witnesses_replayed': n, 'max_witness_height': max(heights), 'w': w(p)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-r", type=int, default=30)
    parser.add_argument("--max-k", type=int, default=12)
    parser.add_argument('--reject-max-r', type=int, default=6)
    parser.add_argument('--reject-max-k', type=int, default=2)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    t0 = time.perf_counter()
    rows = [check_witnesses(r, k, kind)
            for r in range(3, args.max_r + 1)
            for k in range(args.max_k + 1) for kind in 'AB']
    matches_three_three = all(
        generated_obstruction(3, k, kind) == three_three(kind, k)
        for k in range(args.max_k + 1) for kind in 'AB')
    rejection = []
    for r in range(3, args.reject_max_r + 1):
        for k in range(args.reject_max_k + 1):
            for kind in 'AB':
                t = time.perf_counter()
                rejected = not pruned_sortable(inverse(generated_obstruction(r, k, kind)), r, r)
                rejection.append({'r': r, 'k': k, 'family': kind, 'rejected': rejected,
                                  'seconds': round(time.perf_counter() - t, 3)})
    ok = (matches_three_three and all(x['is_permutation'] for x in rows)
          and all(x['rejected'] for x in rejection))
    result = {
        'status': 'passed' if ok else 'FAILED',
        'scope': 'finite checks of the written construction, not a proof',
        'proof_status': ('written proof; '
                         'kernel-checked in formal/equal'),
        'generated_utc': datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
        'python': platform.python_version(),
        'bounds': {'max_r': args.max_r, 'max_k': args.max_k,
                   'reject_max_r': args.reject_max_r, 'reject_max_k': args.reject_max_k},
        'sources': {path: sha256(ROOT / path) for path in (
            'src/stack_sorting/equal_width.py', 'src/stack_sorting/generalized.py',
            'scripts/verify_equal_width.py', 'scripts/verify_three_three.py',
            'docs/infinite-basis-equal-width-draft.md')},
        'matches_three_three_at_r3': matches_three_three,
        'witnesses_total': sum(x['witnesses_replayed'] for x in rows),
        'members': rows,
        'rejection_by_pruned_exhaustive_search': rejection,
        'seconds_total': round(time.perf_counter() - t0, 2),
    }
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
        print(f"Wrote {args.output}; status: {result['status']}.")
    else:
        print(text, end='')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
