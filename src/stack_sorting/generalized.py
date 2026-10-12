"""Exact experiments for a single generalized top-position (r,s)-stack.

All states are top first. Slot-labelled histories, sortable inputs, and distinct
outputs generated from increasing input are intentionally separate objects.
No arbitrary-parameter greedy completeness is assumed. The first-layer result
is a theorem with a separate written proof; finite experiments are not its proof.
"""
from functools import lru_cache
from itertools import permutations


def _natural(value, name, positive=False):
    if type(value) is not int or value < int(positive):
        raise ValueError(f'{name} must be a {"positive" if positive else "nonnegative"} integer')
    return value


def _parameters(r, s, capacity=None):
    _natural(r, 'r', True)
    _natural(s, 's', True)
    if capacity is not None:
        _natural(capacity, 'capacity')


def _permutation(perm):
    perm = tuple(perm)
    if any(type(x) is not int for x in perm) or sorted(perm) != list(range(1, len(perm)+1)):
        raise ValueError('expected a permutation of 1,...,n')
    return perm


def sorting_witness(perm, r, s, capacity=None):
    """One legal accepting history, or None; full push/pop search, not greedy."""
    perm = _permutation(perm)
    _parameters(r, s, capacity)

    @lru_cache(None)
    def visit(i, stack):
        if i == len(perm) and not stack:
            return ()
        next_output = i-len(stack)+1
        for slot in range(min(s, len(stack))):
            if stack[slot] == next_output:
                tail = visit(i, stack[:slot]+stack[slot+1:])
                if tail is not None:
                    return (('O', slot),)+tail
        if i < len(perm) and (capacity is None or len(stack) < capacity):
            for slot in range(min(r, len(stack)+1)):
                tail = visit(i+1, stack[:slot]+(perm[i],)+stack[slot:])
                if tail is not None:
                    return (('P', slot),)+tail
        return None
    return visit(0, ())


def replay(perm, history, r, s, capacity=None):
    """Independently replay and check slots, capacity, consumption, and completion."""
    perm = _permutation(perm)
    _parameters(r, s, capacity)
    stack, output, i = [], [], 0
    for kind, slot in history:
        if type(slot) is not int or slot < 0:
            raise ValueError('invalid slot')
        if kind == 'P':
            if i >= len(perm) or slot >= r or slot > len(stack):
                raise ValueError('invalid push')
            if capacity is not None and len(stack) >= capacity:
                raise ValueError('capacity exceeded')
            stack.insert(slot, perm[i])
            i += 1
        elif kind == 'O':
            if slot >= s or slot >= len(stack):
                raise ValueError('invalid pop')
            output.append(stack.pop(slot))
        else:
            raise ValueError('invalid operation')
    if i != len(perm) or stack:
        raise ValueError('incomplete history')
    return tuple(output)


def test_policy(perm, r, s):
    """Eager pop / first-larger insertion; NOT a general complete sorter.

    This policy is used in the proof for lengths <= r+s+1 only.
    Atkinson already gives a (2,3) failure on 2451673.
    """
    perm = _permutation(perm)
    _parameters(r, s)
    stack, history, i, next_output = [], [], 0, 1
    while stack or i < len(perm):
        slot = next((j for j in range(min(s, len(stack)))
                     if stack[j] == next_output), None)
        if slot is not None:
            stack.pop(slot)
            history.append(('O', slot))
            next_output += 1
        elif i < len(perm):
            slot = next((j for j in range(min(r-1, len(stack)))
                         if stack[j] > perm[i]), min(r-1, len(stack)))
            stack.insert(slot, perm[i])
            history.append(('P', slot))
            i += 1
        else:
            return None
    return tuple(history)


def first_layer_patterns(r, s):
    """The r!s! shortest forbidden patterns; materializes only this layer."""
    _parameters(r, s)
    return {alpha+beta+(1,)
            for alpha in permutations(range(2, r+2))
            for beta in permutations(range(r+2, r+s+2))}


def inverse(perm):
    perm = _permutation(perm)
    result = [0]*len(perm)
    for i, value in enumerate(perm):
        result[value-1] = i+1
    return tuple(result)

