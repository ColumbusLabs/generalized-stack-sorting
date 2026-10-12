"""Constructive (3,3) obstruction families.

One generalized top-position (3,3)-stack, not stacks in series. The two
families A(k), B(k) and every single-deletion history below follow
docs/infinite-basis-three-three-draft.md. The theorem is kernel-checked as the
case r = 3 of formal/equal. Finite replays of these histories are checks of the
construction, not its proof. No priority is claimed.
"""

PREFIX = (5, 1, 7, 2, 4, 10, 3, 12, 9, 6)

# Stack (top first) after each output of PREFIX, in the unique surviving
# shape (Lemma 4.1) and in the accepting histories of Section 5.1.
STANDARD = {5: (1, 2, 4, 3), 1: (2, 4, 3), 7: (2, 4, 6, 3), 2: (4, 6, 3),
            4: (6, 3), 10: (6, 3, 9, 8), 3: (6, 9, 8), 12: (6, 9, 11, 8),
            9: (6, 11, 8), 6: (11, 8)}
_TO_TOP = {12: (8, 9, 11, 6), 9: (8, 11, 6), 6: (8, 11)}
PREFIX_DELETION = {
    5: {1: (), 7: (2, 3, 6, 4), 2: (3, 6, 4), 4: (3, 6), 10: (3, 8, 9, 6),
        3: (8, 9, 6), **_TO_TOP},
    1: {5: (2, 3, 4), 7: (2, 3, 6, 4), 2: (3, 6, 4), 4: (3, 6),
        10: (3, 8, 9, 6), 3: (8, 9, 6), **_TO_TOP},
    7: {5: (1, 2, 4, 3), 1: (2, 4, 3), 2: (4, 3), 4: (3,), 10: (3, 8, 9, 6),
        3: (8, 9, 6), **_TO_TOP},
    2: {5: (1, 3, 4), 1: (3, 4), 7: (3, 4, 6), 4: (3, 6), 10: (3, 8, 9, 6),
        3: (8, 9, 6), **_TO_TOP},
    4: {5: (1, 2, 3), 1: (2, 3), 7: (2, 3, 6), 2: (3, 6), 10: (3, 8, 9, 6),
        3: (8, 9, 6), **_TO_TOP},
    10: {5: (1, 2, 4, 3), 1: (2, 4, 3), 7: (2, 4, 6, 3), 2: (4, 6, 3),
         4: (6, 3), 3: (6,), **_TO_TOP},
    3: {5: (1, 2, 4), 1: (2, 4), 7: (2, 4, 6), 2: (4, 6), 4: (6,),
        10: (8, 9, 6), **_TO_TOP},
    12: {**{v: STANDARD[v] for v in (5, 1, 7, 2, 4, 10, 3)},
         9: (6, 8), 6: (8,)},
    9: {**{v: STANDARD[v] for v in (5, 1, 7, 2, 4)},
        10: (6, 3, 8), 3: (6, 8), 12: (6, 8, 11), 6: (8, 11)},
    6: {5: (1, 2, 4, 3), 1: (2, 4, 3), 7: (2, 4, 3), 2: (4, 3), 4: (3,),
        10: (3, 8, 9), 3: (8, 9), 12: (8, 9, 11), 9: (8, 11)},
    11: {**STANDARD, 12: (6, 9, 8), 9: (6, 8), 6: (8,)},
    8: {**{v: STANDARD[v] for v in (5, 1, 7, 2, 4)},
        10: (6, 3, 9), 3: (6, 9), 12: (6, 9, 11), 9: (6, 11), 6: (11,)},
}


def _index(k):
    if type(k) is not int or k < 0:
        raise ValueError('k must be a nonnegative integer')
    return k


def generated_obstruction(name, k):
    """A(k) of length 16+3k or B(k) of length 17+3k (generated orientation)."""
    _index(k)
    out = list(PREFIX)
    for j in range(k):
        out += [15 + 3*j, 13 + 3*j, 11 + 3*j]
    if name == 'A':
        n = 16 + 3*k
        out += [n, 13 + 3*k, 8, 11 + 3*k, 14 + 3*k, 15 + 3*k]
    elif name == 'B':
        n = 17 + 3*k
        out += [15 + 3*k, 13 + 3*k, n, 8, 11 + 3*k, 14 + 3*k, 16 + 3*k]
    else:
        raise ValueError("family name must be 'A' or 'B'")
    if sorted(out) != list(range(1, n + 1)):
        raise AssertionError('not a permutation')
    return tuple(out)


def sortable_obstruction(name, k):
    """The inverse: a sortable-input basis element of the (3,3)-stack."""
    p = generated_obstruction(name, k)
    result = [0] * len(p)
    for i, value in enumerate(p, 1):
        result[value - 1] = i
    return tuple(result)


class _History:
    """Literal (3,3) machine on increasing input; the deleted token is omitted."""

    def __init__(self, values, deleted):
        self.inp, self.ptr, self.deleted = list(values), 0, deleted
        self.stack, self.ops, self.out = [], [], []

    def push(self, x, slot):
        if x == self.deleted:
            return
        if self.ptr >= len(self.inp) or self.inp[self.ptr] != x:
            raise AssertionError(f'push of {x} out of input order')
        if not 0 <= slot <= min(2, len(self.stack)):
            raise AssertionError(f'illegal push slot {slot} for {x}')
        self.stack.insert(slot, x)
        self.ptr += 1
        self.ops.append(('P', slot))

    def pop(self, x):
        if x == self.deleted:
            return
        slot = self.stack.index(x)
        if slot > 2:
            raise AssertionError(f'{x} is at depth {slot}')
        self.stack.pop(slot)
        self.ops.append(('O', slot))
        self.out.append(x)

    def record(self, v):
        """A new maximum: push it at slot zero and pop it at once."""
        self.push(v, 0)
        self.pop(v)

    def follow(self, outputs, table):
        """Realize a table of stacks after each output (Section 5.1)."""
        for v in outputs:
            if v == self.deleted:
                continue
            target = list(table[v])
            if v in self.stack:
                self.pop(v)
            else:
                while self.inp[self.ptr] != v:
                    x = self.inp[self.ptr]
                    above = target[:target.index(x)]
                    self.push(x, sum(1 for t in above if t in self.stack))
                self.record(v)
            if self.stack != target:
                raise AssertionError(f'table mismatch after {v}')


def deletion_witness(name, k, deleted_value):
    """Slot-labelled history generating the deletion, labels kept.

    The input is the increasing list of the remaining values. Every case is
    the one written in Section 5 of the draft; nothing here searches.
    """
    p = generated_obstruction(name, k)
    a = deleted_value
    if a not in p:
        raise ValueError('deleted value must occur in the obstruction')
    q = [v for v in p if v != a]
    h = _History(sorted(q), a)

    def x(j): return 11 + 3*j
    def a_(j): return 13 + 3*j
    def b(j): return 14 + 3*j
    def rec(j): return 15 + 3*j

    # Phase 1 (Section 5.1).
    if a in PREFIX_DELETION:
        h.follow(PREFIX, PREFIX_DELETION[a])
        regime = 'Z' if a == 8 else 'T'
    else:
        h.follow(PREFIX, STANDARD)
        regime = 'S'

    # Triples (Sections 5.2 and 5.3).
    for j in range(k):
        if regime == 'S':
            if a == rec(j):
                h.record(a_(j)); h.pop(x(j)); regime = 'T'
            elif a == a_(j):
                h.push(b(j), 2); h.record(rec(j)); h.pop(x(j)); regime = 'T'
            elif a == b(j):
                h.push(a_(j), 2); h.record(rec(j)); h.pop(a_(j)); h.pop(x(j))
                regime = 'T'
            else:
                h.push(a_(j), 1); h.push(b(j), 2); h.record(rec(j))
                h.pop(a_(j)); h.pop(x(j))
        elif regime == 'T':
            if h.inp[h.ptr] == x(j):
                h.push(x(j), 1)
            h.push(a_(j), 1); h.push(b(j), 2); h.record(rec(j))
            h.pop(a_(j)); h.pop(x(j))
        else:
            h.push(a_(j), 1); h.push(b(j), 2); h.record(rec(j))
            h.pop(a_(j)); h.pop(x(j))

    # Final block (Sections 5.2 and 5.4).
    xk, ak, bk = x(k), a_(k), b(k)
    n = len(p)
    if name == 'A':
        ck = 15 + 3*k
        if regime in 'TZ':
            if regime == 'T' and h.ptr < len(h.inp) and h.inp[h.ptr] == xk:
                h.push(xk, 1)
            h.push(ak, 1); h.push(bk, 2); h.push(ck, 2); h.record(n)
            for v in (ak, 8, xk, bk, ck):
                h.pop(v)
        elif a == n:
            h.record(ak); h.pop(8); h.pop(xk); h.record(bk); h.record(ck)
        elif a == ak:
            h.push(bk, 2); h.push(ck, 2); h.record(n)
            for v in (8, xk, bk, ck):
                h.pop(v)
        elif a in (bk, ck):
            h.push(ak, 1); h.push(bk, 2); h.push(ck, 2); h.record(n)
            for v in (ak, 8, xk, bk, ck):
                h.pop(v)
        else:
            raise AssertionError('uncovered deletion')
    else:
        rk, d = 15 + 3*k, 16 + 3*k
        if regime in 'TZ':
            if regime == 'T' and h.inp[h.ptr] == xk:
                h.push(xk, 1)
            h.push(ak, 1); h.push(bk, 2); h.record(rk); h.pop(ak)
            h.push(d, 2); h.record(n)
            for v in (8, xk, bk, d):
                h.pop(v)
        elif a == rk:
            h.record(ak); h.push(bk, 2); h.push(d, 2); h.record(n)
            for v in (8, xk, bk, d):
                h.pop(v)
        elif a == ak:
            h.push(bk, 2); h.record(rk); h.push(d, 2); h.record(n)
            for v in (8, xk, bk, d):
                h.pop(v)
        elif a == n:
            h.push(ak, 1); h.push(bk, 2); h.record(rk); h.pop(ak)
            h.pop(8); h.pop(xk); h.pop(bk); h.record(d)
        elif a in (bk, d):
            h.push(ak, 1); h.push(bk, 2); h.record(rk); h.pop(ak)
            h.push(d, 2); h.record(n)
            for v in (8, xk, bk, d):
                h.pop(v)
        else:
            raise AssertionError('uncovered deletion')

    if h.out != q or h.stack or h.ptr != len(h.inp):
        raise AssertionError('history does not generate the deletion')
    return tuple(h.ops)
