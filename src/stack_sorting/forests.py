"""Mechanism-only canonical constraint-forest recurrence.

Trees are tuples of their child trees; leaves are (). Forests are tuples of
rooted trees. The recurrence uses no pattern basis or known coefficients.
See docs/canonical-forests.md for the bijection and
docs/first-return-derivation.md for the finite generating-function derivation.
"""
from functools import lru_cache


def forest_counts(max_n=8):
    """Return counts 0..max_n and memo-state count; explicit bound 0..12."""
    if type(max_n) is not int or not 0 <= max_n <= 12:
        raise ValueError('max_n must be an integer from 0 to 12')
    @lru_cache(None)
    def count(remaining_inputs, forest=(), can_pop=True):
        if remaining_inputs == 0 and not forest:
            return 1
        result = 0
        if remaining_inputs:
            # Bypass consumes one input and emits it.
            result += count(remaining_inputs-1, forest, True)
            if forest:
                # Insert new smaller root above the first tree.
                result += count(remaining_inputs-1, ((forest[0],),)+forest[1:], False)
                # Insert new leaf as first child of first root.
                result += count(remaining_inputs-1, (((),)+forest[0],)+forest[1:], False)
            else:
                result += count(remaining_inputs-1, ((),), False)
        if can_pop and forest:
            result += count(remaining_inputs, forest[0]+forest[1:], True)
            if forest[0] == () and len(forest) >= 2:
                result += count(remaining_inputs, ((),)+forest[1]+forest[2:], True)
        return result
    values = [count(n) for n in range(max_n+1)]
    return values, count.cache_info().currsize
