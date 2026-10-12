"""Exact composition-state recognition for a single generalized (2,s)-stack.

Requires s >= 2. Public permutation predicates distinguish increasing-input
outputs from sortable inputs by inversion. States describe sets of physical
orders, not individual histories. See docs/composition-normal-form.md.
"""
from .generalized import _natural, _permutation, inverse


def _pop_width(s, minimum=2):
    if type(s) is not int or s < minimum:
        raise ValueError(f'pop width must be an integer >= {minimum}')


def block_delete(a, k, t):
    """Exact interval-block image; k is ascending rank and t accessible slots."""
    if (type(a) is not int or type(k) is not int or type(t) is not int
            or not 1 <= k <= a or t < 1):
        raise ValueError('require 1 <= k <= a and t >= 1')
    t = min(t, a)
    if k > a-t+1:
        return (a-1,) if a > 1 else ()
    return ((t-1,) if t > 1 else ()) + (1,)*(a-t-k+1) + ((k-1,) if k > 1 else ())


def _pop(c, rank, s):
    h, above = sum(c), 0
    for j, a in enumerate(c):
        below = h-above-a
        if below < rank <= below+a:
            if above >= s:
                return None
            return c[:j]+block_delete(a, rank-below, s-above)+c[j+1:]
        above += a
    return None


def _record(c, jump):
    if c:
        return (c[0]+jump-1,)+c[1:]
    return (jump-1,) if jump > 1 else ()


def recognizes_generated(perm, pop_width, capacity=None):
    """Whether increasing input can generate perm, optionally at physical capacity H."""
    p = _permutation(perm)
    _pop_width(pop_width)
    if capacity is not None:
        _natural(capacity, 'capacity')
    maximum, held, state = 0, [], ()
    for value in p:
        if value > maximum:
            jump = value-maximum
            if capacity is not None and len(held)+jump > capacity:
                return False
            state = _record(state, jump)
            held.extend(range(maximum+1, value))
            maximum = value
        else:
            rank = held.index(value)+1
            state = _pop(state, rank, pop_width)
            if state is None:
                return False
            held.pop(rank-1)
    return not state


def is_sortable(perm, pop_width, capacity=None):
    """Whether perm is sortable by top-two pushes / top-pop_width pops."""
    return recognizes_generated(inverse(perm), pop_width, capacity)


def infinite_basis_generated(pop_width, m):
    """One minimal forbidden GENERATED output, length 2*s+2+2*m, s >= 3.

    Its inverse is a sortable-input basis element. This explicit family is not
    asserted to be the complete basis.
    """
    _pop_width(pop_width, 3)
    _natural(m, 'm')
    s = pop_width
    maximum = s+2+2*m
    n = maximum+s
    return ((s+2, 1)+tuple(range(3, s+1))
            + tuple(v for j in range(m) for v in (s+4+2*j, s+1+2*j))
            + (n, 2, s+1+2*m)+tuple(range(maximum+1, n)))


def infinite_basis_sortable(pop_width, m):
    """Inverse of infinite_basis_generated: an unsortable input basis element."""
    return inverse(infinite_basis_generated(pop_width, m))


def permutation_counts(pop_width, max_n, state_limit=250000):
    """Exact distinct permutation counts through an explicit maximum length.

    A dynamic program counts unique output codes and bounds total tokens read
    by max_n. It is exponential in general, despite quadratic single-input
    recognition. The explicit state limit raises rather than truncating.
    """
    _pop_width(pop_width)
    _natural(max_n, 'max_n')
    _natural(state_limit, 'state_limit', True)
    current, result = {(): 1}, [1]
    for output_count in range(max_n):
        following = {}
        for state, count in current.items():
            height = sum(state)
            for jump in range(1, max_n-output_count-height+1):
                target = _record(state, jump)
                following[target] = following.get(target, 0)+count
            for rank in range(1, height+1):
                target = _pop(state, rank, pop_width)
                if target is not None:
                    following[target] = following.get(target, 0)+count
            if len(following) > state_limit:
                raise RuntimeError('explicit composition state limit exceeded')
        current = following
        result.append(current.get((), 0))
    return result
