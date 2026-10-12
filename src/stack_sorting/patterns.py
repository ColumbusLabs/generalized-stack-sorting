"""Independent published-basis oracle; unused by mechanical search."""
from itertools import combinations
from . import validate_permutation

BASIS = ((2,3,4,5,1), (2,3,5,4,1), (3,2,4,5,1), (3,2,5,4,1),
         (2,4,5,1,6,3), (2,4,6,1,5,3), (4,2,5,1,6,3), (4,2,6,1,5,3))
# OEIS A393395, offset 0, retrieved 2026-10-09. Prior data, not computed here.
OEIS = (1,1,2,6,24,116,628,3636,21956,136428,865700)


def standardize(values):
    """Relative ranks of pairwise-distinct values."""
    rank = {value: i+1 for i, value in enumerate(sorted(values))}
    return tuple(rank[value] for value in values)


def avoids_basis(perm):
    perm = validate_permutation(perm)
    for length in (5, 6):
        forbidden = {p for p in BASIS if len(p) == length}
        for indices in combinations(range(len(perm)), length):
            if standardize(tuple(perm[i] for i in indices)) in forbidden:
                return False
    return True
