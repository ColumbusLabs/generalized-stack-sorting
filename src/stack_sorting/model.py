"""Exact (2,2)-stack experiments; all stack tuples are top first.

The definition is insertion in position 0 or 1 and removal from position 0
or 1. This is one generalized stack, not two stacks in series. The search
counts operation histories only when explicitly requested; sortable
permutations are counted once regardless of the number of witnesses.
"""
from functools import lru_cache
from itertools import permutations
from . import validate_permutation as validate


def _transitions(perm, state):
    """Private transitions on reachable sorted-prefix states; zero-based slots.

    Precondition: perm is validated; 0 <= i <= n; stack contains exactly the
    consumed entries not yet output, top first. All previous pops emitted
    1..(i-len(stack)). Public searches construct only states satisfying this.
    """
    i, stack = state
    next_output = i - len(stack) + 1
    for pos in range(min(2, len(stack))):
        if stack[pos] == next_output:
            yield ('O', pos), (i, stack[:pos] + stack[pos+1:])
    if i < len(perm):
        for pos in range(min(2, len(stack)+1)):
            yield ('P', pos), (i+1, stack[:pos] + (perm[i],) + stack[pos:])


def sorting_witness(perm):
    """Return one accepting history, or None. Empty input has empty witness."""
    perm = validate(perm)
    @lru_cache(None)
    def visit(i, stack):
        if i == len(perm) and not stack:
            return ()
        for op, child in _transitions(perm, (i, stack)):
            suffix = visit(*child)
            if suffix is not None:
                return (op,) + suffix
        return None
    return visit(0, ())


def is_sortable(perm):
    return sorting_witness(perm) is not None


def history_count(perm):
    """Count all accepting slot-labelled histories, not permutations."""
    perm = validate(perm)
    @lru_cache(None)
    def visit(i, stack):
        if i == len(perm) and not stack:
            return 1
        return sum(visit(*child) for _, child in _transitions(perm, (i, stack)))
    return visit(0, ())


def replay(perm, history):
    """Independently replay a full history; reject impossible or incomplete moves."""
    perm = validate(perm)
    stack, output, i = [], [], 0
    for kind, pos in history:
        if type(pos) is not int or pos not in (0, 1):
            raise ValueError('invalid slot')
        if kind == 'P':
            if i >= len(perm) or pos > len(stack):
                raise ValueError('invalid push')
            stack.insert(pos, perm[i])
            i += 1
        elif kind == 'O':
            if pos >= len(stack):
                raise ValueError('invalid pop')
            output.append(stack.pop(pos))
        else:
            raise ValueError('unknown operation')
    if i != len(perm) or stack:
        raise ValueError('incomplete history')
    return tuple(output)


def inverse(perm):
    perm = validate(perm)
    result = [0] * len(perm)
    for i, value in enumerate(perm):
        result[value-1] = i+1
    return tuple(result)


def generated_permutations(n):
    """Independently generate distinct outputs from increasing input.

    This enumerates output-prefix states. Its output set is the inverse of
    the sortable-input set; it must not be compared to that set literally.
    Intended only for small n because it materializes all prefix states.
    """
    if type(n) is not int or n < 0:
        raise ValueError('n must be a nonnegative integer')
    current = {(0, (), ())}
    for _ in range(2*n):
        following = set()
        for i, stack, output in current:
            if i < n:
                for pos in range(min(2, len(stack)+1)):
                    following.add((i+1, stack[:pos]+(i+1,)+stack[pos:], output))
            for pos in range(min(2, len(stack))):
                following.add((i, stack[:pos]+stack[pos+1:], output+(stack[pos],)))
        current = following
    return {output for i, stack, output in current if i == n and not stack}


def greedy_fixed_push(perm, preferred_slot):
    """Deliberately naive policy: pop next value if available, else fixed-slot push."""
    perm = validate(perm)
    if preferred_slot not in (0, 1):
        raise ValueError('slot must be 0 or 1')
    i, stack = 0, ()
    while i < len(perm) or stack:
        next_output = i - len(stack) + 1
        pos = next((p for p in range(min(2, len(stack))) if stack[p] == next_output), None)
        if pos is not None:
            stack = stack[:pos] + stack[pos+1:]
        elif i < len(perm):
            pos = min(preferred_slot, len(stack))
            stack = stack[:pos] + (perm[i],) + stack[pos:]
            i += 1
        else:
            return False
    return True


def naive_counterexample(preferred_slot, max_n=7):
    for n in range(max_n+1):
        for perm in permutations(range(1,n+1)):
            if is_sortable(perm) and not greedy_fixed_push(perm, preferred_slot):
                return perm
    return None


def atkinson_witness(perm):
    """Prior greedy algorithm from Atkinson (1998), Section 4.

    Pop the next required value whenever it is in the first two slots.
    Otherwise insert the next input so the first two top-first values increase.
    This explicit top-first convention avoids the source wording ambiguity; see docs.
    Source: https://www.cs.otago.ac.nz/staffpriv/mike/Papers/Genstack/Genstack.pdf
    This implementation is separately checked against exhaustive reachability;
    the project does not claim the algorithm as a new result.
    """
    perm = validate(perm)
    stack, history, i, next_output = [], [], 0, 1
    while i < len(perm) or stack:
        position = next((p for p, value in enumerate(stack[:2]) if value == next_output), None)
        if position is not None:
            stack.pop(position)
            history.append(('O', position))
            next_output += 1
        elif i < len(perm):
            position = 0 if not stack or perm[i] < stack[0] else 1
            stack.insert(position, perm[i])
            history.append(('P', position))
            i += 1
        else:
            return None
    return tuple(history)
