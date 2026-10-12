#!/usr/bin/env python3
"""Bounded, reproducible checks; these experiments are not a proof.

Runs locally, with the standard library only. Raw searches are isolated with
explicit time and address-space limits. A resource limit is an error, never a
negative sorting result. No hosted CI or network access is used.
"""
import argparse
from datetime import datetime, timezone
import hashlib
from itertools import permutations
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from stack_sorting.generalized import inverse, replay, sorting_witness  # noqa: E402
from stack_sorting.unequal_basis import (  # noqa: E402
    bounded_drop_count, delete_value, deletion_witness, generated_obstruction,
)

BASE_HEAD = '87b7650379fd656808dfb3b6146f2e2125277ab7'
REFERENCE_BLOB = '912e60e85825a37becc72a162db91ac3fc8ed429'


class StateLimitExceeded(RuntimeError):
    """No acceptance/rejection conclusion is available from an aborted search."""


def normalized_generation(p, r, s, capacity=None, state_limit=100000):
    """Enumerate literal physical orders, not abstract composition states.

    Completeness relative to arbitrary histories uses the written lazy-input
    lemma; this is deliberately distinguished from the unrestricted raw oracle.
    """
    p = tuple(p)
    if (any(type(v) is not int for v in p)
            or sorted(p) != list(range(1, len(p) + 1))):
        raise ValueError('expected a permutation')
    if any(type(w) is not int or w < 1 for w in (r, s, state_limit)):
        raise ValueError('widths and state limit must be positive integers')
    if capacity is not None and (type(capacity) is not int or capacity < 0):
        raise ValueError('capacity must be a nonnegative integer')
    states, maximum, peak, height_peak = {()}, 0, 1, 0
    for wanted in p:
        if wanted > maximum:
            for value in range(maximum + 1, wanted + 1):
                following = set()
                for stack in states:
                    if capacity is not None and len(stack) >= capacity:
                        continue
                    for slot in range(min(r, len(stack) + 1)):
                        following.add(stack[:slot] + (value,) + stack[slot:])
                        if len(following) > state_limit:
                            raise StateLimitExceeded('physical-state limit exceeded')
                states = following
                peak = max(peak, len(states))
                if not states:
                    return {'accepted': False, 'peak_states': peak,
                            'peak_height': height_peak}
                height_peak = max(height_peak, len(next(iter(states))))
            maximum = wanted
        following = set()
        for stack in states:
            slot = stack.index(wanted)
            if slot < s:
                following.add(stack[:slot] + stack[slot + 1:])
        states = following
        if not states:
            return {'accepted': False, 'peak_states': peak,
                    'peak_height': height_peak}
    return {'accepted': () in states, 'peak_states': peak,
            'peak_height': height_peak}


def literal_replay(perm, history, r, s, capacity):
    """Separate implementation: check input, slots, transient height and output."""
    cursor, stack, output, peak = 0, [], [], 0
    for kind, slot in history:
        if type(slot) is not int or slot < 0:
            raise AssertionError('invalid operation index')
        if kind == 'P':
            if cursor >= len(perm) or slot >= r or slot > len(stack):
                raise AssertionError('invalid push')
            stack.insert(slot, perm[cursor])
            cursor += 1
            peak = max(peak, len(stack))
            if peak > capacity:
                raise AssertionError('capacity exceeded')
        elif kind == 'O':
            if slot >= s or slot >= len(stack):
                raise AssertionError('invalid pop')
            output.append(stack.pop(slot))
        else:
            raise AssertionError('invalid operation kind')
    if cursor != len(perm) or stack:
        raise AssertionError('incomplete history')
    return tuple(output), peak


def reverse_dual_history(history):
    """Reverse operations and exchange pushes/pops without changing slots."""
    return tuple(('O' if kind == 'P' else 'P', slot)
                 for kind, slot in reversed(history))


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def verify_witnesses(max_r, max_s, max_m):
    start = time.perf_counter()
    families = histories = operations = 0
    largest_length = largest_height = 0
    for r in range(2, max_r + 1):
        for s in range(r + 1, max_s + 1):
            for m in range(max_m + 1):
                p = generated_obstruction(r, s, m)
                assert len(p) == 2*s + r + 2*m
                assert sorted(p) == list(range(1, len(p) + 1))
                families += 1
                largest_length = max(largest_length, len(p))
                for d in range(1, len(p) + 1):
                    q = delete_value(p, d)
                    history = deletion_witness(r, s, m, d)
                    identity = tuple(range(1, len(q) + 1))
                    out, peak = literal_replay(identity, history, r, s, s + 2)
                    assert out == q
                    # The unchanged repository checker sees the inverse input.
                    assert replay(inverse(q), history, r, s, s + 2) == identity
                    # Independent physical reversal verifies the dual orientation.
                    dual_input = tuple(len(q) + 1 - x for x in reversed(q))
                    dual = reverse_dual_history(history)
                    assert replay(dual_input, dual, s, r, s + 2) == identity
                    histories += 1
                    operations += len(history)
                    largest_height = max(largest_height, peak)
    return {'status': 'passed', 'parameter_ranges': {
                'r': [2, max_r], 's': ['r+1', max_s], 'm': [0, max_m]},
            'family_instances': families, 'single_deletion_histories': histories,
            'operations_per_replay_pass': operations, 'replay_passes': 3,
            'largest_original_length': largest_length,
            'largest_observed_height': largest_height,
            'seconds': time.perf_counter() - start}


def verify_physical_states():
    start = time.perf_counter()
    cases, total_deletions, peak = [], 0, 1
    for r, s in ((2, 3), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6)):
        for m in range(4):
            p = generated_obstruction(r, s, m)
            # No capacity imposed in this rejection search. The lazy input
            # itself bounds the transient height; normalization is still used.
            intact = normalized_generation(p, r, s, state_limit=50000)
            assert not intact['accepted']
            case_peak = intact['peak_states']
            for d in p:
                answer = normalized_generation(delete_value(p, d), r, s,
                                               s + 2, state_limit=50000)
                assert answer['accepted']
                case_peak = max(case_peak, answer['peak_states'])
                total_deletions += 1
            peak = max(peak, case_peak)
            cases.append({'r': r, 's': s, 'm': m, 'n': len(p),
                          'intact_rejected': True, 'all_deletions_accepted': True,
                          'deletion_capacity': s + 2, 'peak_states': case_peak})
    # Intentionally extend the formula outside its API's strict inequality.
    # At (3,3,m=1), a single deletion still fails: it is NOT a basis element.
    diagonal = (5, 1, 7, 2, 9, 4, 11, 3, 6, 8, 10)
    negative = normalized_generation(delete_value(diagonal, 1), 3, 3)
    assert not negative['accepted']
    return {'status': 'passed', 'state_limit': 50000,
            'family_instances': len(cases), 'single_deletions': total_deletions,
            'peak_states': peak, 'cases': cases,
            'negative_control': {'widths': [3, 3], 'm': 1, 'deleted_value': 1,
                                 'deletion_still_rejected': True},
            'seconds': time.perf_counter() - start}


def verify_low_capacity(max_n=6):
    start = time.perf_counter()
    checks = 0
    configurations = ((1, 2), (2, 1), (2, 3), (3, 2), (3, 4), (4, 3))
    for r, s in configurations:
        for h in range(max(r, s) + 2):
            for n in range(max_n + 1):
                accepted = 0
                for p in permutations(range(1, n + 1)):
                    drop = max((i - v for i, v in enumerate(p, 1)), default=-1)
                    expected = not p or (h > 0 and drop < h)
                    answer = normalized_generation(inverse(p), r, s, h)
                    assert answer['accepted'] == expected, (r, s, h, p)
                    accepted += answer['accepted']
                    checks += 1
                assert accepted == bounded_drop_count(n, h)
    return {'status': 'passed', 'widths': [list(c) for c in configurations],
            'capacity_range': '0 through max(r,s)+1 inclusive',
            'max_n': max_n, 'individual_machine_comparisons': checks,
            'seconds': time.perf_counter() - start}


def raw_child(r, s, m):
    # POSIX address-space guard; the larger failed exploratory search is not run.
    import resource
    limit = 1024 * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    start = time.perf_counter()
    p = generated_obstruction(r, s, m)
    witness = sorting_witness(inverse(p), r, s)  # all raw push/pop choices
    assert witness is None
    return {'r': r, 's': s, 'm': m, 'n': len(p),
            'unbounded_raw_rejection': True, 'seconds': time.perf_counter()-start}


def verify_raw():
    cases = []
    for r, s, m in ((2, 3, 0), (2, 3, 2), (3, 4, 0), (3, 4, 1)):
        try:
            completed = subprocess.run(
                [sys.executable, str(Path(__file__).resolve()), '--raw-child',
                 str(r), str(s), str(m)], capture_output=True, text=True, timeout=15,
                check=True)
            cases.append(json.loads(completed.stdout))
        except subprocess.TimeoutExpired:
            cases.append({'r': r, 's': s, 'm': m, 'status': 'incomplete',
                          'reason': '15-second resource limit',
                          'unbounded_raw_rejection': None})
        except subprocess.CalledProcessError as exc:
            reason = ('address-space limit' if 'MemoryError' in (exc.stderr or '')
                      else 'child process failed; not a mathematical rejection')
            cases.append({'r': r, 's': s, 'm': m, 'status': 'incomplete',
                          'reason': reason, 'returncode': exc.returncode,
                          'unbounded_raw_rejection': None})
    status = ('passed' if all(c.get('unbounded_raw_rejection') is True
                              for c in cases) else 'incomplete')
    return {'status': status, 'cases': cases, 'timeout_seconds_per_case': 15,
            'address_space_limit_mib_per_case': 1024,
            'scope': 'original generalized.sorting_witness; no capacity or lazy restriction'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-r', type=int, default=5)
    parser.add_argument('--max-s', type=int, default=7)
    parser.add_argument('--max-m', type=int, default=4)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--raw-child', nargs=3, type=int, help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.raw_child is not None:
        print(json.dumps(raw_child(*args.raw_child)))
        return
    if args.max_r < 2 or args.max_s < 3 or args.max_m < 0:
        parser.error('require max-r >= 2, max-s >= 3 and max-m >= 0')
    reference = (ROOT / 'src/stack_sorting/generalized.py').read_bytes()
    if git_blob(reference) != REFERENCE_BLOB:
        raise RuntimeError('reference generalized.py does not match the fixed repository blob')
    start = time.perf_counter()
    result = {
        'status': 'running', 'base_head': BASE_HEAD,
        'started_at_utc': datetime.now(timezone.utc).isoformat(),
        'python': platform.python_version(),
        'claim_boundary': 'finite validation, not an all-parameter proof or independent review',
        'reference_generalized_git_blob': REFERENCE_BLOB,
        'constructive_replay': verify_witnesses(args.max_r, args.max_s, args.max_m),
        'normalized_physical_state_search': verify_physical_states(),
        'low_capacity_classification': verify_low_capacity(),
        'unrestricted_raw_search': verify_raw(),
        'prior_incomplete_experiment': {
            'r': 4, 's': 5, 'm': 0, 'n': 14,
            'method': 'unrestricted raw original-machine search, without the later memory guard',
            'outcome': 'process killed by execution environment',
            'reason': 'not established; no rejection or acceptance inferred',
            'included_as_passed_evidence': False},
        'prior_guarded_retry': {
            'r': 3, 's': 4, 'm': 1, 'address_space_limit_mib': 512,
            'outcome': 'MemoryError; retried below a 1024-MiB limit',
            'included_as_passed_evidence': False},
        'not_run': ['full original repository unit suite', 'original package CLI',
                    'Lean certificates', 'independent mathematical review'],
    }
    source_paths = ['src/stack_sorting/unequal_basis.py',
                    'src/stack_sorting/generalized.py',
                    'scripts/verify_unequal_basis.py', 'tests/test_unequal_basis.py',
                    'docs/infinite-basis-unequal-draft.md',
                    'docs/unequal-basis-source-audit.md']
    result['sha256'] = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                        for name in source_paths}
    result['seconds_total'] = time.perf_counter() - start
    result['status'] = ('passed' if result['unrestricted_raw_search']['status']
                        == 'passed' else 'incomplete')
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
        print(f"Wrote {args.output.name}; verification status: {result['status']}.")
    else:
        print(text, end='')
    if result['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
