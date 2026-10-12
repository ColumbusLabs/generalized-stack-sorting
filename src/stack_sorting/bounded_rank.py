"""Fixed-rank-window research recognizer with a finite tagged stack alphabet.

For fixed offset q, transition decisions inspect only a bounded top window.
This reference implementation still copies/hashes whole Python tuples and lists;
its runtime is not height-independent. The proof compiles the bounded decision
logic to ordinary pushdown microsteps. Decoding is a separate diagnostic only.
"""
from functools import lru_cache
from . import three_push as normal

UNARY = frozenset('ZOBT')


def encode(state):
    out = []
    for atom in state:
        if type(atom) is int:
            out.extend(('[',) + ('X',) * atom + ('c',))
        else:
            out.append(atom)
    return tuple(out)


def decode(stack):
    """Unbounded diagnostic; never used by transitions."""
    out = []
    i = 0
    while i < len(stack):
        atom = stack[i]
        if atom in UNARY:
            out.append(atom)
            i += 1
            continue
        assert atom == '['
        j = i + 1
        while j < len(stack) and stack[j] == 'X':
            j += 1
        size = j - i - 1
        assert size > 0 and stack[j] in ('b', 'c')
        out.extend(('B',) * size if stack[j] == 'b' else normal.clause(size))
        i = j + 1
    return tuple(out)


def height_cap_two(stack):
    """Bounded peek, implementable by popping/restoring this bounded suffix."""
    count = 0
    for cell in reversed(stack):
        if cell in UNARY or cell == 'X':
            count += 1
            if count == 2:
                return 2
    return count


def push(stack):
    return stack + (('Z', 'B', 'T')[height_cap_two(stack)],)


def _finish_run(work, tag, extra=0):
    """Finish the partially retained run without traversing its old length."""
    work.extend(('X',) * extra)
    if work[-1] == '[':
        work.pop()
    elif tag == 'c' and work[-2] == '[':
        work.pop()
        work.pop()
        work.append('Z')
    else:
        work.append(tag)


@lru_cache(None)
def pop_offset(stack, q):
    if type(q) is not int or q < 0:
        raise ValueError('nonnegative offset required')
    work = list(stack)
    suffix = ()
    remaining = q
    while work:
        atom = work.pop()
        if atom in UNARY:
            if remaining:
                suffix = (atom,) + suffix
                remaining -= 1
                continue
            changed = normal.f0(suffix) if atom == 'Z' else normal.f1(suffix) if atom == 'O' else normal.union01(suffix)
            return None if changed is None else tuple(work) + encode(changed)
        assert atom in ('b', 'c'), (stack, q, atom)
        taken = 0
        while taken <= remaining and work[-1] == 'X':
            work.pop()
            taken += 1
        if taken <= remaining:
            assert work.pop() == '['
            block = ('B',) * taken if atom == 'b' else normal.clause(taken)
            suffix = block + suffix
            remaining -= taken
            continue
        # Selected coordinate belongs to this partially retained counter run.
        r = remaining
        if atom == 'b':
            changed = normal.union01(('B',) * r + suffix)
            if changed is None:
                return None
            _finish_run(work, 'b')
            return tuple(work) + encode(changed)
        if r >= 2 or r >= 1 and suffix:
            changed = normal.f0(('B',) * r + suffix)
            if changed is None:
                return None
            _finish_run(work, 'b')
            return tuple(work) + encode(changed)
        if r == 1:  # suffix empty
            _finish_run(work, 'c', 1)
            return tuple(work)
        if not suffix:
            _finish_run(work, 'b')
            return tuple(work)
        special = normal.exceptional(suffix)
        if special is not None and special[1] in ('O', 'B'):
            _finish_run(work, 'c', special[0] + 1)
            return tuple(work)
        changed = normal.f0(suffix)
        if changed is None:
            return None
        _finish_run(work, 'b')
        return tuple(work) + encode(changed)
    return None


def tokens(permutation):
    held = []
    maximum = 0
    result = []
    for value in permutation:
        if value > maximum:
            result.extend(('P',) * (value - maximum - 1))
            result.append('R')
            held.extend(range(maximum + 1, value))
            maximum = value
        else:
            index = held.index(value)
            result.append(len(held) - index - 1)
            held.pop(index)
    return tuple(result)


def accepts(permutation, d):
    stack = ()
    for token in tokens(permutation):
        if token == 'P':
            stack = push(stack)
        elif token != 'R':
            if token >= d:
                return False
            stack = pop_offset(stack, token)
            if stack is None:
                return False
    return not stack


def counts_through(max_n, d):
    """Count unique token words; x counts P and R, with H of weight one."""
    @lru_cache(None)
    def count(stack, pushing, remaining):
        total = int(not stack and not pushing and remaining == 0)
        if remaining:
            total += count(push(stack), True, remaining - 1)
            total += count(stack, False, remaining - 1)
        if not pushing:
            for q in range(d):
                changed = pop_offset(stack, q)
                if changed is not None:
                    total += count(changed, False, remaining)
        return total
    result = [count((), False, n) for n in range(max_n + 1)]
    return result, count.cache_info().currsize
