"""Bounded original-machine validation of the explicit infinite-family formula.

The written proof, not this finite census, establishes the infinite theorem.
Run with PYTHONPATH=src. No nonstandard packages are required.
"""
import hashlib
import json
from pathlib import Path
from time import perf_counter
from stack_sorting import generalized as g
from stack_sorting import two_push as t


def deletion(p, i):
    x = p[i]
    return tuple(v-int(v > x) for j, v in enumerate(p) if i != j)


def main():
    start, records, checks = perf_counter(), [], 0
    selected = [(3, m) for m in range(4)]+[(4, m) for m in range(2)]+[(5, 0)]
    for s, m in selected:
        p = t.infinite_basis_sortable(s, m)
        assert g.sorting_witness(p, 2, s) is None, (s, m, 'original rejected')
        checks += 1
        witness_hashes = []
        for i in range(len(p)):
            q = deletion(p, i)
            witness = g.sorting_witness(q, 2, s, s+2)
            assert witness is not None, (s, m, i)
            assert g.replay(q, witness, 2, s, s+2) == tuple(range(1, len(q)+1))
            witness_hashes.append(hashlib.sha256(repr((q, witness)).encode()).hexdigest())
            checks += 1
        records.append({'s': s, 'm': m, 'n': len(p), 'unsortable_input': p,
                        'single_deletions_sorted_at_capacity': s+2,
                        'witness_sha256': witness_hashes})
        print('original reachability PASS', s, m, len(p), flush=True)
    formula_checks = 0
    for s in range(3, 11):
        for m in range(31):
            p = t.infinite_basis_generated(s, m)
            assert not t.recognizes_generated(p, s)
            formula_checks += 1
            for i in range(len(p)):
                assert t.recognizes_generated(deletion(p, i), s, s+2), (s, m, i)
                formula_checks += 1
    result = {'status': 'pass', 'scope': 'finite checks, not the infinite-family proof',
              'original_reachability_cases': checks, 'composition_cases': formula_checks,
              'composition_s_range': [3, 10], 'composition_m_range': [0, 30],
              'max_original_n': max(r['n'] for r in records),
              'max_composition_n': 82, 'records': records,
              'duration_seconds': perf_counter()-start,
              'source_sha256': {Path(module.__file__).name:
                  hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
                  for module in (g, t)}}
    destination = Path('evidence/two-push-infinite-family-census.json')
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}, indent=2))


if __name__ == '__main__':
    main()
