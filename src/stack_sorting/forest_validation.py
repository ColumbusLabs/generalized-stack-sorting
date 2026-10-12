"""Independent labelled-path test of the proposed constraint-forest bijection."""
from collections import Counter
from itertools import permutations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
from time import perf_counter
from .model import atkinson_witness, sorting_witness, replay
from .forests import forest_counts
from .leaf_words import word_counts, word_histories
from .algebra import first_return_series, cubic_residual, elimination_polynomial

def paths(n):
    if type(n) is not int or not 0 <= n <= 7:
        raise ValueError("labelled path bound must be an integer from 0 to 7")
    # Labelled tree: (input-introduction token ID, tuple of children).
    def walk(introduced, forest, can_pop, output, history):
        if introduced == n and not forest:
            perm = [0] * n
            for value, token in enumerate(output, 1):
                perm[token - 1] = value
            yield tuple(perm), history
            return
        if introduced < n:
            token = introduced + 1
            yield from walk(token, forest, True, output+(token,), history+(('B',0),))
            if not forest:
                yield from walk(token, ((token,()),), False, output, history+(('P',0),))
            else:
                yield from walk(token, ((token,(forest[0],)),)+forest[1:], False, output, history+(('P',0),))
                root, children = forest[0]
                yield from walk(token, ((root,((token,()),)+children),)+forest[1:], False, output, history+(('P',1),))
        if can_pop and forest:
            token, children = forest[0]
            yield from walk(introduced, children+forest[1:], True, output+(token,), history+(('O',0),))
            if not children and len(forest)>1:
                token, children2 = forest[1]
                yield from walk(introduced, forest[:1]+children2+forest[2:], True, output+(token,), history+(('O',1),))
    yield from walk(0, (), True, (), ())


def expand(history):
    return tuple(operation for op in history for operation in ((('P',0),('O',0)) if op[0]=='B' else (op,)))


def run(bound=6):
    if type(bound) is not int or not 0 <= bound <= 7:
        raise ValueError("bound must be an integer from 0 to 7")
    rows=[]
    for n in range(bound+1):
        start=perf_counter();multiplicities=Counter();canonical_mismatches=[];replay_failures=[]
        forest_history_set=set()
        for perm, compressed in paths(n):
            multiplicities[perm]+=1
            forest_history_set.add(compressed)
            expanded=expand(compressed)
            if expanded != atkinson_witness(perm):canonical_mismatches.append(perm)
            if replay(perm,expanded)!=tuple(range(1,n+1)):replay_failures.append(perm)
        exact={p for p in permutations(range(1,n+1)) if sorting_witness(p) is not None}
        words=list(word_histories(n))
        language_matches=(len(words)==len(set(words)) and set(words)==forest_history_set)
        rows.append({'n':n,'paths':sum(multiplicities.values()),'distinct_permutations':len(multiplicities),'duplicates':sum(v-1 for v in multiplicities.values()),'missing_from_forest':sorted(exact-set(multiplicities)),'extra_in_forest':sorted(set(multiplicities)-exact),'canonical_mismatches':canonical_mismatches,'replay_failures':replay_failures,'word_history_language_matches':language_matches,'elapsed_seconds':round(perf_counter()-start,6)})
    return rows


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=6)
    args = parser.parse_args(argv)
    try:
        rows = run(args.max_n)
    except ValueError as error:
        parser.error(str(error))
    counts, states = forest_counts(8)
    quotient_counts, quotient_states = word_counts(8)
    series = first_return_series(12)
    long_counts, _ = forest_counts(12)
    polynomial = elimination_polynomial()
    passed = all(not row[key] for row in rows for key in
                 ('duplicates', 'missing_from_forest', 'extra_in_forest',
                  'canonical_mismatches', 'replay_failures'))
    passed = passed and all(row['word_history_language_matches'] for row in rows)
    passed = passed and quotient_counts == counts and series['f'] == long_counts
    passed = passed and cubic_residual(series['f']) == [0]*13
    passed = passed and polynomial == {(1,3):2,(1,2):-2,(0,2):-3,(1,1):-1,(0,1):7,(0,0):-4}
    package = Path(__file__).parent
    result = {'kind':'finite-bijection-and-algebra-validation', 'status':'passed' if passed else 'failed',
              'timestamp_utc':datetime.now(timezone.utc).isoformat(),
              'python':platform.python_version(), 'labelled_path_max_n':args.max_n,
              'unlabelled_recurrence_max_n':8, 'unlabelled_recurrence_counts':counts,
              'memo_states':states, 'rows':rows,
              'leaf_word_counts':quotient_counts, 'leaf_word_memo_states':quotient_states,
              'first_return_series_order':12, 'first_return_series':series,
              'forest_counts_through_12':long_counts,
              'cubic_residual_through_12':cubic_residual(series['f']),
              'exact_elimination_coefficients':[{'x_power':i,'f_power':j,'coefficient':v} for (i,j),v in sorted(polynomial.items())],
              'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(package.glob('*.py'))},
              'limitations':['Finite validation supports the separate bijection argument; it is not that proof.',
                             'The all-length derivation is in proof documents; finite checks alone do not prove it.']}
    print(json.dumps(result,indent=2))
    return 0 if passed else 1


if __name__=='__main__':
    raise SystemExit(main())
