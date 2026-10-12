"""Constructive unequal-width obstruction family.

One generalized top-position stack, not stacks in series. The family uses
2 <= r < s. Public sorting obstructions also support the dual r > s case.
No finite experiment is claimed as an all-parameter proof or priority evidence.
See docs/infinite-basis-unequal-draft.md.
"""


def _integer(value, name, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError(f'{name} must be an integer >= {minimum}')
    return value


def _widths(r, s, m):
    _integer(r, 'push width', 2)
    _integer(s, 'pop width', 2)
    _integer(m, 'relay count')
    if r >= s:
        raise ValueError('the generated family requires 2 <= r < s')


def _inverse(p):
    result = [0] * len(p)
    for i, value in enumerate(p, 1):
        result[value - 1] = i
    return tuple(result)


def generated_obstruction(r, s, m):
    """An explicit generated-output obstruction of length 2*s+r+2*m.

    All single deletions have the constructive capacity-(s+2) witnesses below.
    """
    _widths(r, s, m)
    result = [value for i in range(r - 1)
              for value in (s + 2 + 2*i, i + 1)]
    result.extend(range(r + 1, s + 1))
    maximum = s + 2*r - 2
    result.extend(value for j in range(m)
                  for value in (maximum + 2 + 2*j, s + 1 + 2*j))
    maximum += 2*m
    n = maximum + s - r + 2
    result.extend((n, r))
    result.extend(s + 1 + 2*j for j in range(m, m + r - 1))
    result.extend(range(maximum + 1, n))
    return tuple(result)


def sortable_obstruction(r, s, m):
    """Sortable-input basis candidate for unequal widths r,s >= 2.

    Inversion exchanges generation and sorting. The r > s case additionally
    uses the capacity-preserving reverse-complement/inverse sorting duality.
    """
    _integer(r, 'push width', 2)
    _integer(s, 'pop width', 2)
    _integer(m, 'relay count')
    if r == s:
        raise ValueError('equal widths are outside this theorem')
    if r < s:
        return _inverse(generated_obstruction(r, s, m))
    p = generated_obstruction(s, r, m)
    return tuple(len(p) + 1 - value for value in reversed(p))


def delete_value(p, value):
    """Delete a value and standardize a permutation (not an index deletion)."""
    p = tuple(p)
    if any(type(x) is not int for x in p) or sorted(p) != list(range(1, len(p) + 1)):
        raise ValueError('expected a permutation of 1,...,n')
    _integer(value, 'deleted value', 1)
    if value > len(p):
        raise ValueError('deleted value is not in the permutation')
    return tuple(x - int(x > value) for x in p if x != value)


def deletion_witness(r, s, m, deleted_value):
    """Return a literal P/O-slot history generating one standardized deletion.

    This is a deterministic constructive proof witness, not a search. Replay
    it on increasing input to obtain the generated deletion; replay it on the
    inverse deletion to sort that input. All transient heights are <= s+2.
    The internal checks deliberately raise if any construction invariant fails.
    """
    p = generated_obstruction(r, s, m)
    _integer(deleted_value, 'deleted value', 1)
    if deleted_value > len(p):
        raise ValueError('deleted value is not in the obstruction')
    d = deleted_value
    permanent = r
    initial_records = [s + 2 + 2*i for i in range(r - 1)]
    initial_relays = {s + 1 + 2*i for i in range(r - 1)}
    lows = [x for x in range(1, r + 1) if x != d]

    # Prescribe the order after reading the first r (originally labelled) lows.
    if d < r:
        target = [permanent] + [x for x in lows if x != permanent]
    elif d in initial_records:
        last = initial_records.index(d) + 1
        target = [permanent] + [x for x in lows if x not in (permanent, last)] + [last]
    elif r < d <= s or d in initial_relays:
        last = r - 1
        target = [permanent] + [x for x in lows if x not in (permanent, last)] + [last]
    else:
        target = lows
    target_index = {x: i for i, x in enumerate(target)}
    source = [x for x in range(1, len(p) + 1) if x != d]
    requested = [x for x in p if x != d]
    remaining_lows = {x for x in range(1, r) if x != d}
    stack, history = [], []
    consumed = 0

    def push(slot):
        nonlocal consumed
        if not (0 <= slot < r and slot <= len(stack)):
            raise AssertionError('construction used an invalid push slot')
        if consumed >= len(source) or len(stack) >= s + 2:
            raise AssertionError('construction exceeded input or physical capacity')
        stack.insert(slot, source[consumed])
        consumed += 1
        history.append(('P', slot))

    # This small prefill is intentional when the first record was deleted.
    # It uses at most r slots and is a legal, possibly non-lazy history.
    for x in lows:
        slot = sum(target_index[y] < target_index[x] for y in stack)
        push(slot)
    if stack != target:
        raise AssertionError('initial low-order construction failed')

    for wanted in requested:
        while consumed < len(source) and source[consumed] <= wanted:
            x = source[consumed]
            if x == wanted:
                slot = 0  # the requested new maximum bypasses immediately
            elif remaining_lows:
                slot = min(r - 1, len(stack))
            elif permanent in stack and stack.index(permanent) <= r - 2:
                slot = stack.index(permanent) + 1  # shelter the permanent token
            else:
                slot = min(r - 1, len(stack))
            push(slot)
        slot = stack.index(wanted)
        if slot >= s:
            raise AssertionError('construction requested an inaccessible output')
        stack.pop(slot)
        history.append(('O', slot))
        remaining_lows.discard(wanted)
    if consumed != len(source) or stack:
        raise AssertionError('construction did not complete')
    return tuple(history)


def bounded_drop_count(n, capacity):
    """Low-capacity class count, valid when H <= max(r,s)+1 (r,s positive).

    This counts permutations with maximum drop <= H-1, not operation histories.
    Empty input is counted once; capacity zero accepts only empty input.
    """
    from math import factorial
    _integer(n, 'length')
    _integer(capacity, 'capacity')
    if n == 0:
        return 1
    if capacity == 0:
        return 0
    if n <= capacity:
        return factorial(n)
    return factorial(capacity) * capacity**(n - capacity)
