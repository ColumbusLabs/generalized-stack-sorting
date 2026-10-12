#!/usr/bin/env python3
"""Bounded, reproducible checks of the (3,3) families; these are not a proof.

Standard library only; runs locally; no hosted CI or network access. For each
k <= --max-k it checks, for A(k) and B(k):
- that the member is a permutation of 1..n;
- rejection, by an exhaustive search over lazy histories with two sound
  prunings (independent of the written rejection argument);
- that every single-deletion witness of stack_sorting.three_three replays, via
  the repository's unchanged generalized.replay, to the standardized deletion;
- the maximum physical height of each witness and the statistic w(p).
The optional --unpruned-a0 runs the repository's unpruned sorting_witness on
A(0) in a subprocess with an address-space limit. A resource stop is recorded
as STOPPED and is never read as a sorting result; a 'generated' result
contradicts the rejection argument and makes the whole check FAIL.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from stack_sorting.generalized import inverse, replay  # noqa: E402
from stack_sorting.three_three import (  # noqa: E402
    deletion_witness, generated_obstruction,
)


def pruned_sortable(pi, r=3, s=3):
    """Exhaustive search for a sorting history of pi, with two sound prunings.

    (1) If the next required output is already in a poppable slot, pop it at
    once: any successful continuation that first pushes can be reordered to pop
    first (each later insertion slot stays legal, lowered by one if it lay
    below the popped token), reaching the same stack.
    (2) Discard a stack in which a held token has at least s larger tokens
    above it: those must be output after it and never change relative order,
    so it can never reach a poppable slot.
    """
    n = len(pi)
    failed = set()
    sys.setrecursionlimit(max(10000, 20 * n))

    def go(i, st):
        st = list(st)
        out = i - len(st) + 1
        moved = True
        while moved:
            moved = False
            for k in range(min(s, len(st))):
                if st[k] == out:
                    del st[k]
                    out += 1
                    moved = True
                    break
        if i == n:
            return not st
        key = (i, tuple(st))
        if key in failed:
            return False
        x = pi[i]
        for j in range(min(r, len(st) + 1)):
            ns = st[:j] + [x] + st[j:]
            if any(sum(1 for t in ns[:k] if t > ns[k]) >= s for k in range(len(ns))):
                continue
            if go(i + 1, ns):
                return True
        failed.add(key)
        return False

    return go(0, ())


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


def check_member(name, k):
    p = generated_obstruction(name, k)
    n = len(p)
    t0 = time.perf_counter()
    rejected = not pruned_sortable(inverse(p))
    t_rej = time.perf_counter() - t0
    heights = []
    t0 = time.perf_counter()
    for a in p:
        ops = deletion_witness(name, k, a)
        q = [v for v in p if v != a]
        rank = {v: i + 1 for i, v in enumerate(sorted(q))}
        if replay(tuple(range(1, n)), ops, 3, 3) != tuple(rank[v] for v in q):
            raise AssertionError(f'replay mismatch {name}({k}) deleting {a}')
        heights.append(height(ops))
    return {
        'family': name, 'k': k, 'length': n,
        'is_permutation': sorted(p) == list(range(1, n + 1)),
        'rejected_by_pruned_exhaustive_search': rejected,
        'deletion_witnesses_replayed': n,
        'max_witness_height': max(heights),
        'w': w(p),
        'seconds_rejection': round(t_rej, 4),
        'seconds_witnesses': round(time.perf_counter() - t0, 4),
    }


UNPRUNED = """
import sys
sys.path.insert(0, {src!r})
sys.setrecursionlimit(100000)
from stack_sorting.generalized import inverse, sorting_witness
from stack_sorting.three_three import generated_obstruction
p = generated_obstruction('A', 0)
print('rejected' if sorting_witness(inverse(p), 3, 3) is None else 'generated')
"""


def unpruned_a0(limit_bytes, seconds):
    import resource

    def limit():
        resource.setrlimit(resource.RLIMIT_AS, (limit_bytes, limit_bytes))

    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [sys.executable, '-c', UNPRUNED.format(src=str(ROOT / 'src'))],
            capture_output=True, text=True, timeout=seconds, preexec_fn=limit)
        out = proc.stdout.strip()
        status = out if proc.returncode == 0 and out in ('rejected', 'generated') else 'STOPPED'
    except subprocess.TimeoutExpired:
        status = 'STOPPED'
    return {'member': 'A(0)', 'checker': 'generalized.sorting_witness (unpruned)',
            'status': status, 'address_space_limit_bytes': limit_bytes,
            'time_limit_seconds': seconds,
            'seconds': round(time.perf_counter() - t0, 2)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-k', type=int, default=6)
    parser.add_argument('--unpruned-a0', action='store_true')
    parser.add_argument('--memory-gb', type=float, default=6.0)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    if args.max_k < 0:
        parser.error('--max-k must be nonnegative')
    t0 = time.perf_counter()
    rows = [check_member(name, k) for k in range(args.max_k + 1) for name in 'AB']
    ok = all(r['is_permutation'] and r['rejected_by_pruned_exhaustive_search'] for r in rows)
    result = {
        'status': None,
        'scope': 'finite checks of the written construction, not a proof',
        'proof_status': ('written proof; '
                         'kernel-checked as the case r = 3 of formal/equal'),
        'generated_utc': datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
        'python': platform.python_version(),
        'max_k': args.max_k,
        'sources': {path: sha256(ROOT / path) for path in (
            'src/stack_sorting/three_three.py',
            'src/stack_sorting/generalized.py',
            'scripts/verify_three_three.py',
            'docs/infinite-basis-three-three-draft.md')},
        'members': rows,
        'deletion_witnesses_total': sum(r['deletion_witnesses_replayed'] for r in rows),
        'max_witness_height': {name: max(r['max_witness_height'] for r in rows if r['family'] == name)
                               for name in 'AB'},
        'w': {name: sorted({r['w'] for r in rows if r['family'] == name}) for name in 'AB'},
    }
    if args.unpruned_a0:
        result['unpruned_a0'] = unpruned_a0(int(args.memory_gb * 2**30), 1800)
        # A generated A(0) would contradict the rejection proof: fail loudly.
        # A STOPPED run is inconclusive and does not change the status.
        if result['unpruned_a0']['status'] == 'generated':
            ok = False
    result['status'] = 'passed' if ok else 'FAILED'
    result['seconds_total'] = round(time.perf_counter() - t0, 2)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
        print(f"Wrote {args.output}; status: {result['status']}.")
    else:
        print(text, end='')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
