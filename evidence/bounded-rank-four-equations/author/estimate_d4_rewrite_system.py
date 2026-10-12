"""Small exact guarded-rule size estimate; no grammar elimination or fitting."""
from itertools import product
from pathlib import Path
import json
from stack_sorting import bounded_rank as tagged
from stack_sorting import three_push as normal


def suffixes(n):
    if not n:
        yield (), ()
        return
    for a in ('Z', 'O', 'B', 'T'):
        for cells, state in suffixes(n - 1):
            yield (a,) + cells, (a,) + state
    for m in range(1, n + 1):
        for cells, state in suffixes(n - m):
            yield ('[',) + ('X',) * m + ('b',) + cells, ('B',) * m + state
            if m >= 2:
                yield ('[',) + ('X',) * m + ('c',) + cells, (m,) + state


def estimate(d=4, return_rules=False):
    grouped = {}
    rejected = 0
    candidate = 0
    for q in range(d):
        rules = set()
        for tail_cells, _ in suffixes(q):
            for selected in ('Z', 'O', 'B', 'T'):
                old = (selected,) + tail_cells
                changed = tagged.pop_offset(old, q)
                candidate += 1
                if changed is None:
                    rejected += 1
                else:
                    rules.add((old[::-1], changed[::-1]))
        for r in range(q + 1):
            for tail_cells, _ in suffixes(q - r):
                for kind in ('b', 'c'):
                    for left in (0, 1, 2):
                        m = left + r + 1
                        if kind == 'c' and m == 1:
                            continue
                        old = ('[',) + ('X',) * m + (kind,) + tail_cells
                        changed = tagged.pop_offset(old, q)
                        candidate += 1
                        if changed is None:
                            rejected += 1
                            continue
                        # left=2 represents every left>=2. The opening delimiter
                        # and any earlier X cells remain untouched and unread.
                        preserved = 1 if left == 2 else 0
                        if preserved:
                            assert changed[0] == '['
                        rules.add((old[preserved:][::-1], changed[preserved:][::-1]))
        grouped[q] = rules
    if return_rules:
        return grouped
    # A prefix-matching PDA can share all common left-side prefixes for each H_q.
    prefixes = set()
    endings = set()
    for q, rules in grouped.items():
        for before, after in rules:
            for k in range(len(before) + 1):
                prefixes.add((q, before[:k]))
            endings.add((q, before, after))
    # Check that left guards for one command are disjoint prefix cylinders.
    for q, rules in grouped.items():
        words = sorted(before for before, _ in rules)
        assert len(set(words)) == len(words), ('nondeterministic right sides', q)
        for i, word in enumerate(words[:-1]):
            assert words[i+1][:len(word)] != word, ('overlapping left guards', q, word, words[i+1])
    return {'d': d, 'candidate_guarded_held_rules': candidate,
            'rejected_guarded_cases': rejected,
            'successful_guarded_held_rules': {q: len(v) for q,v in grouped.items()},
            'held_prefix_trie_nodes': len(prefixes),
            'maximum_left_guard_cells': max(len(a) for rr in grouped.values() for a,b in rr),
            'maximum_replacement_cells': max(len(b) for rr in grouped.values() for a,b in rr),
            'naive_full_triple_grammar_bound': 9*(len(prefixes)+2)**2,
            'scope': 'Guarded held-rewrite and prefix-trie estimate only. P/R control, reachable-state pruning, productive grammar extraction, and equations not yet built.'}


if __name__ == '__main__':
    result = estimate()
    Path('d4-rewrite-size-estimate.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
