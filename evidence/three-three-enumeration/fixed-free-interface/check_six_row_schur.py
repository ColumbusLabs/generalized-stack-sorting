#!/usr/bin/env python3
"""Exact rank-six certificate using only degree-four completion coefficients."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,time,resource
import check_minor as base

ROWS=base.ROWS+[('Z','Z','T')]
COLS=[(),('B',),('T','T'),('T','T','T'),('T',),('B','B')]
D=4
start=time.monotonic()
H=[[[base.count(P+W,m) for m in range(D+1)] for W in COLS] for P in ROWS]
source=Path(__file__).resolve().parent/'author-rank-six-coefficients.json'
author=json.loads(source.read_text())
assert author['row_initial_states']==[list(P) for P in ROWS]
assert author['column_words']==[list(W) for W in COLS]
assert H==author['matrix_entry_coefficients']
core=base.determinant([[H[i][j] for j in range(4)] for i in range(4)])
assert core[0]==-1728
border=[];schur=[]
for i in [4,5]:
    br=[];sr=[]
    for j in [4,5]:
        minor=base.determinant([[H[r][c] for c in list(range(4))+[j]] for r in list(range(4))+[i]])
        br.append(minor)
        quotient=[]
        for n in range(D+1):quotient.append((Fraction(minor[n])-sum(core[k]*quotient[n-k] for k in range(1,n+1)))/core[0])
        assert all(v.denominator==1 for v in quotient)
        sr.append([int(v) for v in quotient])
    border.append(br);schur.append(sr)
expected=[[[0,0,0,0,0],[0,0,0,0,24]],[[0,0,0,0,12],[0,0,0,0,48]]]
assert schur==expected
leading=core[0]*(schur[0][0][4]*schur[1][1][4]-schur[0][1][4]*schur[1][0][4]);assert leading==497664
ranks=[]
for m in [3,4]:
    block=[[H[a][b][i-j] if i>=j else 0 for j in range(m+1) for b in range(6)] for i in range(m+1) for a in range(6)]
    ranks.append({'degree':m,'dimension':len(block),'rank_mod_1000000007':base.rank(block)})
assert [r['rank_mod_1000000007'] for r in ranks]==[16,22]
out={'status':'EXACT common-context series rank at least SIX','scope':'Common fixed/free port family only; no rank claim beyond four for the narrower ZB-only family','row_initial_states':ROWS,'column_words':COLS,'coefficient_bound':D,'matrix_entry_coefficients':H,'core_determinant_coefficients':core,'bordered_five_by_five_determinants':border,'schur_complement_entry_coefficients':schur,'exact_six_by_six_determinant_leading_term':{'degree':8,'coefficient':leading},'why_degree_four_suffices':'All Schur entries vanish below degree four; their degree-four coefficient matrix has determinant -288. Unknown higher coefficients cannot affect degree eight. Multiply by core constant determinant -1728.','modular_cross_checks':ranks,'memo_states':base.count.cache_info().currsize,'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'helper_sha256':hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),'independent_transition_sha256':hashlib.sha256(Path(base.ind.__file__).read_bytes()).hexdigest(),'author_table_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
Path('independent-six-row-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
