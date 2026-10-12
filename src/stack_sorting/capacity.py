"""Physical-capacity refinements of the generalized top-two-position stack.

The original machine has no bypass: an immediate push/pop still occupies one
slot. Bounded compressed-word checks therefore require a spare slot for B.
Finite agreement here is not a proof of capacity optimality or novelty.
"""
from functools import lru_cache
from itertools import permutations
import argparse
import json
import time

from . import validate_permutation
from .model import _transitions, atkinson_witness


def _bound(value, name, maximum=None):
    if type(value) is not int or value < 0 or (maximum is not None and value > maximum):
        raise ValueError(f'{name} must be a nonnegative integer' +
                         (f' at most {maximum}' if maximum is not None else ''))


def minimum_capacity(perm):
    """Exact minimax peak over all sorted-output histories, or None if impossible.

    This explores the original push/pop graph without a canonicality assumption.
    State sufficiency and acyclicity are the same as in the exact recognizer.
    Intended for small inputs; exhaustive use has a factorial input cost.
    """
    perm = validate_permutation(perm)
    @lru_cache(None)
    def visit(i, stack):
        if i == len(perm) and not stack:
            return 0
        best = None
        for _, child in _transitions(perm, (i, stack)):
            suffix_peak = visit(*child)
            if suffix_peak is not None:
                candidate = max(len(stack), suffix_peak)
                best = candidate if best is None else min(best, candidate)
        return best
    return visit(0, ())


def capacity_witness(perm, capacity):
    """Original-machine witness with every held stack at most capacity, or None."""
    perm = validate_permutation(perm)
    _bound(capacity, 'capacity')
    @lru_cache(None)
    def visit(i, stack):
        if i == len(perm) and not stack:
            return ()
        for op, child in _transitions(perm, (i, stack)):
            if len(child[1]) > capacity:
                continue
            tail = visit(*child)
            if tail is not None:
                return (op,) + tail
        return None
    return visit(0, ())


def history_peak(history):
    """Peak of an original-machine history, not a compressed bypass trace."""
    if history is None:
        return None
    height = peak = 0
    for op, _ in history:
        if op not in ('P', 'O'):
            raise ValueError('history must contain only original P/O operations')
        height += 1 if op == 'P' else -1
        if height < 0:
            raise ValueError('negative stack height')
        peak = max(peak, height)
    if height:
        raise ValueError('history does not end empty')
    return peak


def capacity_lower_bound(perm):
    """Zero for empty input; otherwise one plus maximum drop i-perm[i-1].

    A universal physical-storage lower bound, not a sortability test.
    """
    perm = validate_permutation(perm)
    return 0 if not perm else 1 + max(i-value for i, value in enumerate(perm, 1))


def bounded_word_counts(capacity, max_n=12):
    """Count operation-labelled leaf-word paths subject to physical capacity."""
    _bound(capacity, 'capacity', 12)
    _bound(max_n, 'max_n', 20)
    @lru_cache(None)
    def count(remaining, word='', can_pop=True):
        if remaining == 0 and not word:
            return 1
        total = 0
        if remaining and len(word) < capacity:
            total += count(remaining-1, word, True)  # B has transient height +1.
            total += count(remaining-1, 'R'+word if word else 'L', False)
            if word:
                total += count(remaining-1, 'RL'+word[1:], False)
        if can_pop and word:
            total += count(remaining, word[1:], True)
            if word[0] == 'L' and len(word) > 1:
                total += count(remaining, 'L'+word[2:], True)
        return total
    return [count(n) for n in range(max_n+1)]


def _inverse_unit(series):
    assert series[0] == 1
    inverse = [1]
    for n in range(1, len(series)):
        inverse.append(-sum(series[i]*inverse[n-i] for i in range(1, n+1)))
    return inverse


def capacity_series(capacity, order=12):
    """Exact truncated series from the height-indexed first-return recursion.

    k_0=f_0=1; k_h=(1+x-4x*k_(h-1)+2x*f_(h-1))^-1;
    f_h=(1-x*k_(h-1))^-1. This is independent of the path-counting DP.
    """
    _bound(capacity, 'capacity', 100)
    _bound(order, 'order', 100)
    k = f = [1] + [0]*order
    for _ in range(capacity):
        kd = [1] + [(1 if n == 1 else 0)-4*k[n-1]+2*f[n-1]
                    for n in range(1, order+1)]
        fd = [1] + [-k[n-1] for n in range(1, order+1)]
        k, f = _inverse_unit(kd), _inverse_unit(fd)
    return f


def audit_capacity(max_n=6, series_order=12):
    """Bounded exhaustive comparison; explicit max_n <= 8 prevents accidental runs."""
    _bound(max_n, 'max_n', 8)
    _bound(series_order, 'series_order', 20)
    started = time.monotonic()
    rows = []
    for n in range(max_n+1):
        histogram = [0]*(n+1)
        for perm in permutations(range(1, n+1)):
            optimum = minimum_capacity(perm)
            canonical = history_peak(atkinson_witness(perm))
            if optimum != canonical:
                raise AssertionError(('canonical peak mismatch', perm, optimum, canonical))
            if optimum is not None:
                if optimum != capacity_lower_bound(perm):
                    raise AssertionError(('maximum-drop mismatch', perm, optimum))
                histogram[optimum] += 1
        cumulative = [sum(histogram[:h+1]) for h in range(n+1)]
        word = [bounded_word_counts(h, n)[n] for h in range(n+1)]
        if cumulative != word:
            raise AssertionError(('word-count mismatch', n, cumulative, word))
        rows.append({'n':n, 'minimum_peak_histogram':histogram,
                     'capacity_counts':cumulative, 'all_comparisons':'passed'})
    series = {}
    for h in range(max_n+1):
        first_return = capacity_series(h, series_order)
        if first_return != bounded_word_counts(h, series_order):
            raise AssertionError(('height recurrence mismatch', h))
        series[str(h)] = first_return
    return {'kind':'finite physical-capacity experiment','status':'passed',
            'max_n':max_n,'series_order':series_order,'rows':rows,
            'bounded_series':series,'elapsed_seconds':time.monotonic()-started,
            'convention':'B requires one temporary physical slot; capacity zero accepts only empty',
            'limitations':'finite evidence only; no historical priority inferred'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=6, choices=range(9))
    parser.add_argument('--series-order', type=int, default=12, choices=range(21))
    args = parser.parse_args()
    print(json.dumps(audit_capacity(args.max_n, args.series_order), indent=2))


if __name__ == '__main__':
    main()
