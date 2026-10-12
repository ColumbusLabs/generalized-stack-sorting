#!/usr/bin/env python3
"""Bounded check that the (r,s)-stack and the (Av(S_r + 1), s)-machine generate
the same permutations (Proposition 5.1 of docs/classification-paper.md).

Standard library only; local; no hosted CI. The (r,s)-stack inserts the next
input entry at a slot j <= min(r-1, height) and removes an entry of depth at
most s-1, with no bypass. The (C,s)-machine (Albert-Homberger-Pantone-Shar-
Vatter containers, with Vatter's s-pop) may bypass, may push the next input
entry anywhere in the container provided the contents avoid S_r + 1 (no entry
has r smaller entries before it), and may pop any of the leftmost s entries.
The machine is checked with and without bypass. All run in generating mode on
input 1..n. This is a finite check, not a proof.
"""
import argparse
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import platform
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CASES = '1,1,8;2,1,7;1,2,7;2,2,8;2,3,8;3,2,8;3,3,7;2,4,7;4,2,7;3,4,7'


def contains_Sr_plus_1(word, r):
    return any(sum(1 for y in word[:i] if y < x) >= r for i, x in enumerate(word))


def generated_stack(n, r, s):
    out = set()

    @lru_cache(maxsize=None)
    def go(nxt, stack, done):
        if nxt > n and not stack:
            out.add(done)
            return
        if nxt <= n:
            for j in range(min(r - 1, len(stack)) + 1):
                go(nxt + 1, stack[:j] + (nxt,) + stack[j:], done)
        for j in range(min(s, len(stack))):
            go(nxt, stack[:j] + stack[j + 1:], done + (stack[j],))
    go(1, (), ())
    return out


def generated_c_machine(n, r, s, bypass=True):
    out = set()

    @lru_cache(maxsize=None)
    def go(nxt, cont, done):
        if nxt > n and not cont:
            out.add(done)
            return
        if nxt <= n:
            if bypass:
                go(nxt + 1, cont, done + (nxt,))
            for j in range(len(cont) + 1):
                new = cont[:j] + (nxt,) + cont[j:]
                if not contains_Sr_plus_1(new, r):
                    go(nxt + 1, new, done)
        for j in range(min(s, len(cont))):
            go(nxt, cont[:j] + cont[j + 1:], done + (cont[j],))
    go(1, (), ())
    return out


def parse_cases(text):
    cases = []
    for item in text.split(';'):
        r, s, n = (int(v) for v in item.split(','))
        if min(r, s) < 1 or n < 0 or n > 9:
            raise ValueError('need r,s >= 1 and 0 <= n <= 9')
        cases.append((r, s, n))
    return cases


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases', default=DEFAULT_CASES,
                        help='semicolon-separated r,s,max_n triples (max_n <= 9)')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    t0 = time.perf_counter()
    rows, ok = [], True
    for r, s, max_n in parse_cases(args.cases):
        t = time.perf_counter()
        counts, equal = [], True
        for n in range(max_n + 1):
            a = generated_stack(n, r, s)
            counts.append(len(a))
            if not a == generated_c_machine(n, r, s) == generated_c_machine(n, r, s, False):
                equal = False
                break
        ok &= equal
        rows.append({'r': r, 's': s, 'max_n': max_n, 'equal': equal,
                     'counts_by_n': counts, 'seconds': round(time.perf_counter() - t, 3)})
    result = {
        'status': 'passed' if ok else 'FAILED',
        'scope': 'finite check of Proposition 5.1 (docs/classification-paper.md), not a proof',
        'generated_utc': datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
        'python': platform.python_version(),
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'cases': rows,
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
    sys.exit(main())
