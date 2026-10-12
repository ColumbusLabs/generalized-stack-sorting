"""Independent finite leaf/nonleaf-word quotient; operation labels stay distinct."""
from functools import lru_cache


def word_counts(max_n=8):
    if type(max_n) is not int or not 0 <= max_n <= 12:
        raise ValueError('max_n must be an integer from 0 to 12')
    @lru_cache(None)
    def count(remaining, word='', can_pop=True):
        if remaining == 0 and not word:
            return 1
        total = 0
        if remaining:
            total += count(remaining-1, word, True)  # B
            total += count(remaining-1, 'R'+word if word else 'L', False)  # P0
            if word:
                total += count(remaining-1, 'RL'+word[1:], False)  # P1
        if can_pop and word:
            total += count(remaining, word[1:], True)  # O0
            if word[0] == 'L' and len(word)>1:
                total += count(remaining, 'L'+word[2:], True)  # O1
        return total
    values = [count(n) for n in range(max_n+1)]
    return values, count.cache_info().currsize


def word_histories(n):
    """Enumerate labelled quotient histories; small validation bound 0..7."""
    if type(n) is not int or not 0 <= n <= 7:
        raise ValueError('n must be an integer from 0 to 7')
    def walk(remaining, word, can_pop, history):
        if remaining==0 and not word:
            yield history
            return
        if remaining:
            yield from walk(remaining-1, word, True, history+(('B',0),))
            yield from walk(remaining-1, 'R'+word if word else 'L', False, history+(('P',0),))
            if word:
                yield from walk(remaining-1, 'RL'+word[1:], False, history+(('P',1),))
        if can_pop and word:
            yield from walk(remaining, word[1:], True, history+(('O',0),))
            if word[0]=='L' and len(word)>1:
                yield from walk(remaining, 'L'+word[2:], True, history+(('O',1),))
    yield from walk(n, '', True, ())
