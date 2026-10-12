"""Complete generated/sortable basis for one top-position (2,3)-stack.

The classification is a written theorem, not a Lean certificate. Generated
outputs and sortable inputs differ by inversion. These routines list basis
members, not the much larger class of sortable permutations.
"""
from itertools import permutations
from .generalized import _natural, inverse
from .two_push import infinite_basis_generated


def relay_cores(m):
    """Three generated-output basis cores of length 8+2*m, before symmetries."""
    _natural(m, 'm')
    a = infinite_basis_generated(3, m)
    b = tuple(4 if v == 3 else 3 if v == 4 else v for v in a)
    c = ((5, 1, 8, 4, 2, 3, 6, 7) if m == 0
         else a[:2]+(7, 4, 3)+a[5:])
    return a, b, c


def _orbit(core):
    for swap in (False, True):
        p = tuple(3-v if swap and v in (1, 2) else v for v in core)
        for tail in permutations(p[-3:]):
            yield p[:-3]+tail


def generated_basis_at_length(n):
    """All length-n minimal forbidden GENERATED outputs, without duplicates.

    Returns a lexicographically sorted tuple. There are 12 at n=6 or 7,
    36 at every even n>=8, and no others, by the written complete-basis theorem.
    """
    _natural(n, 'n')
    if n == 6:
        cores = ((6, 1, 2, 3, 4, 5),)
    elif n == 7:
        cores = ((5, 1, 7, 2, 3, 4, 6),)
    elif n >= 8 and n % 2 == 0:
        cores = relay_cores((n-8)//2)
    else:
        return ()
    return tuple(sorted({p for core in cores for p in _orbit(core)}))


def sortable_basis_at_length(n):
    """All length-n minimal forbidden SORTABLE inputs, by inversion."""
    return tuple(sorted(inverse(p) for p in generated_basis_at_length(n)))


def basis_count(n):
    """Number of basis elements of length n; not the sortable-class count."""
    _natural(n, 'n')
    if n in (6, 7):
        return 12
    return 36 if n >= 8 and n % 2 == 0 else 0
