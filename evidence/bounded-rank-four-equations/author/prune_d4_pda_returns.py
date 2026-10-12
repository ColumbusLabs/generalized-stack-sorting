"""Sparse Boolean return-summary feasibility probe, with explicit size/time caps."""
from collections import defaultdict, deque
from pathlib import Path
import json
import resource
import time
from estimate_d4_rewrite_system import estimate, suffixes

ALPHABET = tuple('ZOBT[Xbc#')
READY, PUSHING, FINAL = 0, 1, 2


def build_pda(d=4, with_labels=False):
    states = {('ready',): READY, ('pushing',): PUSHING, ('final',): FINAL}
    transitions = []  # p, popped symbol, new control, pushed top-first word, weight
    labels = []  # Input labels retained separately from their counting weights.
    def add_edge(p, symbol, target, word, weight, label):
        transitions.append((p, symbol, target, word, weight))
        labels.append(label)
    def state(name):
        if name not in states:
            states[name] = len(states)
        return states[name]
    def add_command(name, guards, sources, target, weight):
        lookup = {before: after for before, after in sorted(guards)}
        assert len(lookup) == len(guards)
        guard_words=list(lookup)
        assert all(b[:len(a)] != a for a,b in zip(guard_words,guard_words[1:])), 'overlapping guards'
        root = state((name, ()))
        for source in sources:
            for symbol in ALPHABET:
                add_edge(source, symbol, root, (symbol,), weight, name)
        children = set()
        for before in lookup:
            for k, symbol in enumerate(before):
                prefix = before[:k]
                next_prefix = before[:k+1]
                edge = (prefix, symbol, next_prefix)
                if edge in children:
                    continue
                children.add(edge)
                p = state((name, prefix))
                if next_prefix in lookup:
                    add_edge(p, symbol, target, lookup[next_prefix], '1', ())
                else:
                    add_edge(p, symbol, state((name, next_prefix)), (), '1', ())
    held = estimate(d, return_rules=True)
    for q, guards in held.items():
        add_command(('H', q), guards, (READY,), READY, 'y')
    # At a completed command, every reachable nonempty store starts with Z:
    # its smallest held label has coordinate digit zero. Every other possible
    # leading factor (O/B/T/free B run/nontrivial C) permits or forces digit one.
    # Consequently height 0 is #, height 1 is Z#, and every other valid store
    # has height >=2. These shallow guards deliberately use that invariant.
    p_guards = {(('#',), ('Z', '#')), (('Z','#'), ('B','Z','#'))}
    for symbol in ('O','B','T','b','c'):
        p_guards.add(((symbol,), ('T',symbol)))
    for symbol in ('Z','O','B','T','b','c'):
        p_guards.add((('Z',symbol), ('T','Z',symbol)))
    assert len(p_guards)==13
    guards_sorted = sorted(a for a,b in p_guards)
    for i, a in enumerate(guards_sorted[:-1]):
        assert guards_sorted[i+1][:len(a)] != a
    add_command(('P',), p_guards, (READY, PUSHING), PUSHING, 'x')
    for source in (READY, PUSHING):
        for symbol in ALPHABET:
            add_edge(source, symbol, READY, (symbol,), 'x', ('R',))
    add_edge(READY, '#', FINAL, (), '1', ('$',))  # single final end marker
    keys=[(p,a,label) for (p,a,r,word,w),label in zip(transitions,labels)]
    assert len(keys)==len(set(keys)), 'nondeterministic labelled transition'
    epsilon_sources={(p,a) for p,a,label in keys if not label}
    assert not any((p,a) in epsilon_sources and label for p,a,label in keys)
    return (states, transitions, labels) if with_labels else (states, transitions)


def prune(max_pairs=100000, max_seconds=15, minimize=True):
    start = time.monotonic()
    states, transitions, labels = build_pda(with_labels=True)
    if minimize:
        from minimize_d4_pda_controls import quotient
        states,transitions,labels,certificate=quotient(states,transitions,labels)
        Path('d4-control-bisimulation-certificate.json').write_text(json.dumps(certificate,separators=(',',':'))+'\n')
    returns = defaultdict(set)
    watchers = defaultdict(set)
    queue = deque(range(len(transitions)))
    queued = set(queue)
    updates = evaluations = pair_count = 0
    status = 'PASS saturation complete'
    while queue:
        index = queue.popleft()
        queued.remove(index)
        p, a, r, word, weight = transitions[index]
        frontier = {r}
        for symbol in word:
            following = set()
            for source in frontier:
                key = (source, symbol)
                watchers[key].add(index)
                following.update(returns[key])
            frontier = following
            if not frontier:
                break
        key = (p, a)
        new = frontier - returns[key]
        if new:
            returns[key].update(new)
            pair_count += len(new)
            updates += 1
            for dependent in watchers[key]:
                if dependent not in queued:
                    queued.add(dependent)
                    queue.append(dependent)
        evaluations += 1
        if pair_count > max_pairs:
            status = 'STOP pair-count cap reached; no complete system claim'
            break
        if time.monotonic() - start > max_seconds:
            status = 'STOP time cap reached; no complete system claim'
            break
    out = {'status': status, 'control_states': len(states), 'stack_symbols': len(ALPHABET),
           'pda_transitions': len(transitions), 'productive_return_pairs_so_far': pair_count,
           'nonempty_return_rows': sum(bool(v) for v in returns.values()),
           'transition_evaluations': evaluations, 'return_row_updates': updates,
           'queue_remaining': len(queue), 'start_return_targets': sorted(returns[(READY,'#')]),
           'largest_return_row': max(map(len,returns.values()), default=0),
           'seconds': time.monotonic() - start,
           'peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
           'max_pairs': max_pairs, 'max_seconds': max_seconds,
           'scope': 'Boolean productivity only; coaccessibility and weighted production extraction not yet performed.'}
    return out, (states, transitions, returns)


if __name__ == '__main__':
    result, _ = prune()
    Path('d4-pda-return-pruning.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
