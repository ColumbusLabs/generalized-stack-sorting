"""Complete forbidden basis of one top-position (2,4)-stack.

The computer-assisted written proof classifies actual
minimal forbidden permutations. It is not a Lean certificate or a formula
for the sortable class. Generated outputs and sortable inputs are inverses.
"""
from itertools import permutations, product
from .generalized import _natural, inverse

_N2, _N3, _N4 = ('N', 2), ('N', 3), ('N', 4)
_H2, _H3, _H4 = ('H', 2), ('H', 3), ('H', 4)
_A, _B, _C = (_H2, _H3, _H4), (_H2, _H3), (_H3, _H4)
_FINITE_WORDS = (
    {(_N2,)}
    | {(_N3, c) for c in _C}
    | {(a, _N3) for a in _A}
    | {(_N4, c, _H3) for c in _C}
    | {(a, _N4, _H3) for a in _A}
    | {(_N3, _H4, _H3, _H2, _N3)}
    | {(a, _N3, _H3, _H2, _N3) for a in _A}
)
_ENTRY_WORDS = (
    {(a, b) for a, b in product(_A, _B)}
    | {(_N2, c, b, _H2) for c, b in product(_C, _B)}
    | {(a, _N2, b, _H2) for a, b in product(_A, _B)}
)
_EXIT_WORDS = ((_N4,), (_N3, _H2, _N3))


def _middle_words(length):
    """Disjoint finite words and the 32 entry/relay/exit families."""
    words = {w for w in _FINITE_WORDS if len(w) == length}
    for entry, finish in product(_ENTRY_WORDS, _EXIT_WORDS):
        remainder = length-len(entry)-len(finish)
        if remainder >= 0 and remainder % 2 == 0:
            words.add(entry+(_N2, _H2)*(remainder//2)+finish)
    return tuple(sorted(words))


def _decode(code):
    """Pure canonical-code decoding, including the intentionally failed pop."""
    held, output, maximum = [], [], 0
    for kind, value in code:
        if kind == 'N':
            held.extend(range(maximum+1, maximum+value))
            maximum += value
            output.append(maximum)
        else:
            output.append(held.pop(value-1))
    assert not held
    return tuple(output)


def generated_basis_cores_at_length(n):
    """Canonical basis cores: second entry 1 and increasing final four labels."""
    _natural(n, 'n')
    if n == 7:
        return ((7, 1, 2, 3, 4, 5, 6),)
    if n < 8:
        return ()
    return tuple(sorted(
        _decode((('N', 6), ('H', 1))+middle+(('H', 1),)*5)
        for middle in _middle_words(n-7)
    ))


def generated_basis_at_length(n):
    """All distinct length-n minimal forbidden GENERATED outputs, sorted."""
    result = set()
    for core in generated_basis_cores_at_length(n):
        for tail in permutations(core[-4:]):
            p = core[:-4]+tail
            result.add(p)
            result.add(tuple(3-v if v in (1, 2) else v for v in p))
    return tuple(sorted(result))


def sortable_basis_at_length(n):
    """All length-n minimal forbidden SORTABLE inputs, by inversion."""
    return tuple(sorted(inverse(p) for p in generated_basis_at_length(n)))


def basis_count(n):
    """Exact basis count, distinct from the number of sortable permutations."""
    _natural(n, 'n')
    if n in (7, 8):
        return 48
    if n == 9:
        return 240
    if n == 10:
        return 528
    if n == 12:
        return 1248
    return 1536 if n >= 14 and n % 2 == 0 else 0
