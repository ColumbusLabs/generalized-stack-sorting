"""Explicitly bounded, reproducible mechanical-oracle consistency checks."""
import argparse
from datetime import datetime, timezone
import hashlib
from itertools import permutations
import json
from pathlib import Path
import platform
from time import perf_counter
from .model import (sorting_witness, replay, history_count, generated_permutations,
                    inverse, naive_counterexample, atkinson_witness)
from .patterns import avoids_basis, OEIS


def run(max_n=7, generation_max_n=5):
    if type(max_n) is not int or not 0 <= max_n <= 8:
        raise ValueError('max_n must be an integer from 0 to 8')
    if type(generation_max_n) is not int or not 0 <= generation_max_n <= min(max_n, 6):
        raise ValueError('generation_max_n must be from 0 to min(max_n, 6)')
    rows = []
    for n in range(max_n+1):
        start = perf_counter()
        accepted, mismatches = [], []
        replay_failures = 0
        atkinson_mismatches = []
        histories = 0 if n <= 5 else None
        for perm in permutations(range(1,n+1)):
            witness = sorting_witness(perm)
            sortable = witness is not None
            canonical = atkinson_witness(perm)
            if (canonical is not None) != sortable:
                atkinson_mismatches.append(perm)
            if canonical is not None and replay(perm, canonical) != tuple(range(1,n+1)):
                replay_failures += 1
            if sortable != avoids_basis(perm):
                mismatches.append(perm)
            if sortable:
                accepted.append(perm)
                if replay(perm, witness) != tuple(range(1,n+1)):
                    replay_failures += 1
            if histories is not None:
                histories += history_count(perm)
        orientation_matches = None
        if n <= generation_max_n:
            orientation_matches = {inverse(p) for p in generated_permutations(n)} == set(accepted)
        rows.append({'n':n, 'sortable_permutations':len(accepted),
                     'published_count':OEIS[n], 'basis_mismatches':mismatches, 'atkinson_mismatches':atkinson_mismatches,
                     'witness_replay_failures':replay_failures,
                     'accepting_histories':histories,
                     'generation_inverse_matches':orientation_matches,
                     'sorted_accepted_json_sha256':hashlib.sha256(json.dumps(accepted).encode()).hexdigest(),
                     'elapsed_seconds':round(perf_counter()-start,6)})
    counterexamples = []
    for slot in (0,1):
        perm = naive_counterexample(slot, max_n=4)
        counterexamples.append({'policy':'pop next if possible; otherwise fixed preferred push slot',
                               'slot':slot,'first_counterexample':perm,
                               'witness':sorting_witness(perm),
                               'minimality_checked_through_n':4})
    good = all(r['sortable_permutations']==r['published_count'] and not r['basis_mismatches']
               and not r['atkinson_mismatches'] and r['witness_replay_failures']==0 and r['generation_inverse_matches'] is not False
               for r in rows)
    package = Path(__file__).parent
    return {'kind':'experiment', 'status':'passed' if good else 'failed',
            'timestamp_utc':datetime.now(timezone.utc).isoformat(),
            'python':platform.python_version(), 'model':'(2,2)-stack; top-first; sorted output; slot-labelled moves',
            'max_n':max_n, 'generation_max_n':generation_max_n,
            'counterexample_search_max_n':4,
            'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(package.glob('*.py'))},
            'rows':rows, 'counterexamples':counterexamples,
            'limitations':['Finite consistency checks only, not a structural enumeration proof.',
                           'Permutation membership uses one witness; history totals are separately computed.',
                           'Generation checks above the explicit generation bound were not run.',
                           'The known cubic is prior literature, not derived by this computation.']}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=7)
    parser.add_argument('--generation-max-n', type=int, default=5)
    args = parser.parse_args(argv)
    try:
        result = run(args.max_n, args.generation_max_n)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps(result, indent=2))
    return 0 if result['status']=='passed' else 1


if __name__=='__main__':
    raise SystemExit(main())
