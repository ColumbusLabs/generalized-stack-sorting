"""Equal-width (r,r) obstruction families, r >= 3; Lean-checked.

One generalized top-position (r,r)-stack. The families A_r(k), B_r(k) and every
single-deletion history below follow docs/infinite-basis-equal-width-draft.md,
section by section; nothing here searches. At r = 3 they are exactly the
families of stack_sorting.three_three. The theorem is kernel-checked in
formal/equal (Equal.famA, Equal.famB are these families, zero-based). Finite
replays are checks of the construction, not its proof. No priority is claimed.
"""


def _check(r, k):
    if type(r) is not int or r < 3:
        raise ValueError('r must be an integer >= 3')
    if type(k) is not int or k < 0:
        raise ValueError('k must be a nonnegative integer')


def roles(r):
    """Named values of the prefix (Section 2)."""
    q = [r + 2*i for i in range(1, r)]           # Q_1..Q_(r-1)
    e = [r + 1 + 2*j for j in range(r - 1)]      # E_0..E_(r-2)
    return {'Q': q, 'E': e, 'P': r, 'C': 3*r - 1, 'U': 3*r, 'M1': 3*r + 1,
            'V': 3*r + 2, 'M2': 3*r + 3}


def prefix(r):
    v = roles(r)
    out = []
    for i in range(1, r):
        out += [v['Q'][i-1], i]
    return out + [v['E'][0], v['M1'], v['P'], v['M2'], v['U'], v['E'][1]]


def first_old(r):
    """O_0: the tokens above the carrier after the prefix, in output order."""
    v = roles(r)
    return v['E'][2:] + [v['V']]


def generated_obstruction(r, k, kind):
    """A_r(k) (length 3r+7+3k) or B_r(k) (length 3r+8+3k), generated orientation.

    Step j uses a_j = 3r+4+3j, b_j = a_j+1 and the record R_j = a_j+2. It
    outputs R_j, a_j and the oldest token of the queue; b_j joins the queue.
    """
    _check(r, k)
    if kind not in ('A', 'B'):
        raise ValueError("kind must be 'A' or 'B'")
    out = prefix(r)
    queue = first_old(r)
    for j in range(k):
        a = 3*r + 4 + 3*j
        out += [a + 2, a, queue.pop(0)]
        queue.append(a + 1)
    a = 3*r + 4 + 3*k
    carrier = roles(r)['C']
    if kind == 'A':
        out += [a + 3, a, carrier] + sorted(queue) + [a + 1, a + 2]
    else:
        out += [a + 2, a, a + 4, carrier] + sorted(queue) + [a + 1, a + 3]
    if sorted(out) != list(range(1, len(out) + 1)):
        raise AssertionError('not a permutation')
    return tuple(out)


def sortable_obstruction(r, k, kind):
    p = generated_obstruction(r, k, kind)
    result = [0] * len(p)
    for i, value in enumerate(p, 1):
        result[value - 1] = i
    return tuple(result)


class _History:
    """Literal (r,r) machine on increasing input; the deleted token is omitted."""

    def __init__(self, r, values, deleted):
        self.r, self.inp, self.ptr, self.deleted = r, list(values), 0, deleted
        self.stack, self.ops, self.out = [], [], []

    def has(self, x):
        return x in self.stack

    def unread(self, x):
        return x != self.deleted and x in self.inp[self.ptr:]

    def push(self, x, slot):
        if x == self.deleted:
            return
        if self.ptr >= len(self.inp) or self.inp[self.ptr] != x:
            raise AssertionError(f'push of {x} out of input order')
        if not 0 <= slot <= min(self.r - 1, len(self.stack)):
            raise AssertionError(f'illegal slot {slot} for {x} in {self.stack}')
        self.stack.insert(slot, x)
        self.ptr += 1
        self.ops.append(('P', slot))

    def pop(self, x):
        if x == self.deleted:
            return
        slot = self.stack.index(x)
        if slot > self.r - 1:
            raise AssertionError(f'{x} is at depth {slot}')
        self.stack.pop(slot)
        self.ops.append(('O', slot))
        self.out.append(x)

    def record(self, v):
        self.push(v, 0)
        self.pop(v)

    def bottom(self):
        return len(self.stack)

    def above(self, y):
        return self.stack.index(y)

    def below(self, y):
        return self.stack.index(y) + 1


def _standard_q_phase(h, r, v):
    """Section 5.1 (standard Q-phase): lows on top, E_0 and each E_i just above r."""
    q, e, p = v['Q'], v['E'], v['P']
    for t in range(1, r):
        h.push(t, h.bottom())
    h.push(p, h.bottom())
    h.push(e[0], h.above(p) if h.has(p) else h.bottom())
    h.record(q[0])
    h.pop(1)
    for i in range(2, r):
        h.push(e[i-1], h.above(p) if h.has(p) else h.bottom())
        h.record(q[i-1])
        h.pop(i)
    h.pop(e[0])


def _tail_from_x(h, r, v):
    """Section 5.4 (the tail): from X = (r, E_2..E_(r-2), E_1) to L(0)."""
    h.push(v['C'], 1)
    h.push(v['U'], r - 1)
    h.record(v['M1'])
    h.pop(v['P'])
    h.push(v['V'], r - 1)
    h.record(v['M2'])
    h.pop(v['U'])
    h.pop(v['E'][1])


def _prefix_history(h, r, a):
    """Sections 5.1 and 5.4: the prefix with value a deleted (or none)."""
    v = roles(r)
    q, e, p, c = v['Q'], v['E'], v['P'], v['C']
    lows = list(range(1, r))
    if a == q[0]:                                     # (P1) delete Q_1
        h.record(1)
        for t in range(2, r):
            h.push(t, t - 2)
        h.push(p, r - 2)
        h.push(e[0], r - 1)
        h.push(e[1], r - 1)
        h.record(q[1])
        h.pop(2)
        for s in range(3, r):
            h.push(e[s-1], h.above(e[1]))
            h.record(q[s-1])
            h.pop(s)
        h.pop(e[0])
        _tail_from_x(h, r, v)
        return 'L'
    if a in lows or a == e[0] or a in q[1:]:          # (P2) low, E_0 or Q_t
        if a in lows:
            for x in lows:
                h.push(x, h.bottom())
            h.push(p, h.bottom())
            h.push(e[0], h.bottom())
        elif a == e[0]:
            for x in lows:
                h.push(x, h.bottom())
            h.push(p, h.bottom())
        else:
            t = q.index(a) + 1                        # the low t goes to the bottom
            for x in lows:
                h.push(x, min(h.bottom(), t - 1) if x <= t else h.above(t))
            h.push(p, h.above(t))
            h.push(e[0], h.above(t))
        h.record(q[0])
        for s in range(1, r):
            h.pop(s)
            if s == r - 1:
                break
            if q[s] == a:
                continue
            for x in e[1:]:
                if x < q[s] and h.unread(x):
                    if x == e[1]:
                        h.push(x, h.above(e[0]) if h.has(e[0]) else h.below(p))
                    else:
                        h.push(x, h.above(e[1]))
            h.record(q[s])
        h.pop(e[0])
        for x in e[1:]:                               # an E still unread (Q_(r-1) deleted)
            if h.unread(x) and x < v['M1']:
                h.push(x, h.bottom() if x == e[1] else h.above(e[1]))
        _tail_from_x(h, r, v)
        return 'L'
    if a == e[1]:                                     # (P3)
        _standard_q_phase(h, r, v)
        h.push(c, h.above(p))
        h.push(v['U'], r - 1)
        h.record(v['M1'])
        h.pop(p)
        h.push(v['V'], r - 1)
        h.record(v['M2'])
        h.pop(v['U'])
        return 'L'
    if a == v['U']:                                   # (P4)
        _standard_q_phase(h, r, v)
        h.push(c, h.below(p))
        h.record(v['M1'])
        h.pop(p)
        h.push(v['V'], r - 1)
        h.record(v['M2'])
        h.pop(e[1])
        return 'L'
    if a == v['M1']:                                  # (P5)
        for t in range(1, r):
            h.push(t, h.bottom())
        h.push(p, h.bottom())
        h.push(e[0], h.above(p))
        h.record(q[0])
        h.pop(1)
        h.push(e[1], h.above(p))
        h.record(q[1])
        h.pop(2)
        for i in range(3, r):
            h.push(e[i-1], h.above(e[1]))
            h.record(q[i-1])
            h.pop(i)
        h.pop(e[0])
        h.pop(p)
        h.push(c, 0)
        h.push(v['U'], 1)
        h.push(v['V'], r - 1)
        h.record(v['M2'])
        h.pop(v['U'])
        h.pop(e[1])
        return 'L'
    if a == p:                                        # (P6)
        for t in range(1, r):
            h.push(t, h.bottom())
        h.push(e[0], h.bottom())
        h.record(q[0])
        h.pop(1)
        h.push(e[1], h.bottom())
        h.record(q[1])
        h.pop(2)
        for i in range(3, r):
            h.push(e[i-1], h.above(e[1]))
            h.record(q[i-1])
            h.pop(i)
        h.pop(e[0])
        h.push(c, 0)
        h.push(v['U'], 1)
        h.record(v['M1'])
        h.push(v['V'], r - 1)
        h.record(v['M2'])
        h.pop(v['U'])
        h.pop(e[1])
        return 'L'
    if a == v['M2']:                                  # (P7): V stays unread
        _standard_q_phase(h, r, v)
        h.push(c, h.below(p))
        h.push(v['U'], h.below(p))
        h.record(v['M1'])
        h.pop(p)
        h.pop(v['U'])
        h.pop(e[1])
        return 'L'
    # Standard prefix (Section 5.1); a is a later value, an O_0 token or C.
    _standard_q_phase(h, r, v)
    if h.has(c) or h.unread(c):
        h.push(c, h.below(p))
        h.push(v['U'], h.above(c))
    else:
        h.push(v['U'], h.below(p))
    h.record(v['M1'])
    h.pop(p)
    h.push(v['V'], h.above(c) if h.has(c) else h.bottom())
    h.record(v['M2'])
    h.pop(v['U'])
    h.pop(e[1])
    if a == c:
        return 'Z'
    return 'L' if a in first_old(r) else 'S'


def _below_carrier(h, c):
    """Slot just below the carrier (or the top when the carrier is deleted)."""
    return h.below(c) if h.has(c) else 0


def deletion_witness(r, k, kind, deleted_value):
    """Slot-labelled history generating the deletion, labels kept."""
    p = generated_obstruction(r, k, kind)
    a = deleted_value
    if a not in p:
        raise ValueError('deleted value must occur in the obstruction')
    q = [x for x in p if x != a]
    h = _History(r, sorted(q), a)
    c = roles(r)['C']
    regime = _prefix_history(h, r, a)
    queue = list(first_old(r))
    for j in range(k):                                # Sections 5.2 and 5.3
        a0 = 3*r + 4 + 3*j
        b0, rec = a0 + 1, a0 + 2
        head = queue.pop(0)
        if regime == 'S':
            if a == rec:
                h.record(a0)
                h.pop(head)
                regime = 'L'
            elif a == a0:
                h.push(b0, r - 1)
                h.record(rec)
                h.pop(head)
                regime = 'L'
            elif a == b0:
                h.push(a0, r - 1)
                h.record(rec)
                h.pop(a0)
                h.pop(head)
                regime = 'L'
            else:
                h.push(a0, r - 2)
                h.push(b0, r - 1)
                h.record(rec)
                h.pop(a0)
                h.pop(head)
        else:
            for x in sorted(x for x in queue + [head] if h.unread(x)):
                h.push(x, _below_carrier(h, c))
            s = _below_carrier(h, c)
            h.push(a0, s)
            h.push(b0, s + 1)
            h.record(rec)
            h.pop(a0)
            h.pop(head)
        queue.append(b0)
    a0 = 3*r + 4 + 3*k                                # Section 5.5
    rest = sorted(queue)
    if regime != 'S':
        for x in sorted(x for x in queue if h.unread(x)):
            h.push(x, _below_carrier(h, c))
        s = _below_carrier(h, c)
    if kind == 'A':
        b0, c0, n = a0 + 1, a0 + 2, a0 + 3
        tail = rest + [b0, c0]
        if regime != 'S':
            h.push(a0, s)
            h.push(b0, s + 1)
            h.push(c0, s + 1)
            h.record(n)
            h.pop(a0)
            h.pop(c)
        elif a == n:
            h.record(a0)
            h.pop(c)
            for o in rest:
                h.pop(o)
            h.record(b0)
            h.record(c0)
            tail = []
        elif a == a0:
            h.push(b0, r - 1)
            h.push(c0, r - 1)
            h.record(n)
            h.pop(c)
        else:
            h.push(a0, r - 2)
            h.push(b0, r - 1)
            h.push(c0, r - 1)
            h.record(n)
            h.pop(a0)
            h.pop(c)
    else:
        b0, rec, d0, n = a0 + 1, a0 + 2, a0 + 3, a0 + 4
        tail = rest + [b0, d0]
        if regime != 'S':
            h.push(a0, s)
            h.push(b0, s + 1)
            h.record(rec)
            h.pop(a0)
            h.push(d0, _below_carrier(h, c))
            h.record(n)
            h.pop(c)
        elif a == rec:
            h.record(a0)
            h.push(b0, r - 1)
            h.push(d0, r - 1)
            h.record(n)
            h.pop(c)
        elif a == a0:
            h.push(b0, r - 1)
            h.record(rec)
            h.push(d0, r - 1)
            h.record(n)
            h.pop(c)
        elif a == n:
            h.push(a0, r - 2)
            h.push(b0, r - 1)
            h.record(rec)
            h.pop(a0)
            h.pop(c)
            for o in rest:
                h.pop(o)
            h.pop(b0)
            h.record(d0)
            tail = []
        elif a == b0:
            h.push(a0, r - 1)
            h.record(rec)
            h.pop(a0)
            h.push(d0, r - 1)
            h.record(n)
            h.pop(c)
        else:                                          # a == d0
            h.push(a0, r - 2)
            h.push(b0, r - 1)
            h.record(rec)
            h.pop(a0)
            h.record(n)
            h.pop(c)
    for o in tail:
        h.pop(o)
    if h.out != q or h.stack or h.ptr != len(h.inp):
        raise AssertionError('history does not generate the deletion')
    return tuple(h.ops)
