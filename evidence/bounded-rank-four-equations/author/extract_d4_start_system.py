"""Extract only start-coaccessible productive return equations, with size caps."""
from collections import defaultdict, deque
from functools import lru_cache
from pathlib import Path
import json
import time
import resource
from prune_d4_pda_returns import prune, READY, FINAL


def extract(max_variables=100000, max_productions=500000, max_seconds=20):
    start = time.monotonic()
    saturation, (states, transitions, returns) = prune()
    assert saturation['status'].startswith('PASS')
    by_source = defaultdict(list)
    for t in transitions:
        by_source[t[0], t[1]].append(t)
    @lru_cache(None)
    def targets(p, word):
        if not word:
            return frozenset((p,))
        if len(word) == 1:
            return frozenset(returns[p, word[0]])
        result = set()
        for middle in returns[p, word[0]]:
            result.update(targets(middle, word[1:]))
        return frozenset(result)
    def var(p, word, q):
        if not word:
            assert p == q
            return None
        return (p, tuple(word), q)
    initial = var(READY, ('#',), FINAL)
    identifiers = {initial: 0}
    pending = deque((initial,))
    equations = []
    term_count = 0
    def add(v):
        if v is None:
            return None
        if v not in identifiers:
            identifiers[v] = len(identifiers)
            pending.append(v)
        return identifiers[v]
    status = 'PASS start system extracted'
    while pending:
        current = pending.popleft()
        p, word, q = current
        terms = []
        if len(word) == 1:
            for _, _, r, new, weight in by_source[p, word[0]]:
                if q in targets(r, new):
                    child = add(var(r, new, q))
                    terms.append((weight, () if child is None else (child,)))
        else:
            first, tail = word[0], word[1:]
            for middle in sorted(returns[p, first]):
                if q in targets(middle, tail):
                    a = add(var(p, (first,), middle))
                    b = add(var(middle, tail, q))
                    terms.append(('1', tuple(x for x in (a,b) if x is not None)))
        equations.append((identifiers[current], terms))
        term_count += len(terms)
        if len(identifiers) > max_variables or term_count > max_productions:
            status = 'STOP system-size cap reached'
            break
        if time.monotonic() - start > max_seconds:
            status = 'STOP time cap reached'
            break
    metadata = {'status': status, 'd': 4, 'pda_control_states': len(states),
                'productive_return_pairs': saturation['productive_return_pairs_so_far'],
                'start_coaccessible_variables': len(identifiers),
                'equations_processed': len(equations), 'productions': term_count,
                'unfinished_variables': len(pending), 'composition_cache_entries': targets.cache_info().currsize,
                'largest_composition_targets': max((len(targets(p,word)) for p,word,q in identifiers),default=0),
                'seconds': time.monotonic() - start,
                'peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                'scope': 'Explicit unambiguous stack-removal equation system from guarded PDA; algebraic weights P/R=x,H=y.'}
    return metadata, identifiers, equations


if __name__ == '__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-variables',type=int,default=100000)
    parser.add_argument('--max-productions',type=int,default=500000)
    parser.add_argument('--max-seconds',type=float,default=20)
    args=parser.parse_args()
    metadata, identifiers, equations = extract(args.max_variables,args.max_productions,args.max_seconds)
    Path('d4-start-system-size.json').write_text(json.dumps(metadata,indent=2)+'\n')
    if metadata['status'].startswith('PASS'):
        data={'metadata':{k:v for k,v in metadata.items() if k not in ('seconds','peak_rss_kib')}, 'start':0,
              'variables':[{'id':identifier,'control_in':p,'stack_word':''.join(word),'control_out':q}
                           for (p,word,q),identifier in sorted(identifiers.items(),key=lambda kv:kv[1])],
              'equations':[{'lhs':identifier,'terms':[[weight,list(rhs)] for weight,rhs in terms]}
                           for identifier,terms in equations]}
        Path('d4-start-system.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print(json.dumps(metadata,indent=2))
    if not metadata['status'].startswith('PASS'):
        raise SystemExit(1)  # Do not let a shell pipeline reduce a stale prior system.
