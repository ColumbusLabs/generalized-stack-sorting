#!/usr/bin/env python3
"""Independent exact rank-five certificate for common fixed/free contexts."""
from pathlib import Path
from itertools import permutations
from functools import lru_cache
import sys,json,hashlib,time,resource
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/"normal-form-review"))
import independent_check as ind

ROWS=[('Z','B'),('Z','B','B'),('Z','B','T'),('Z','Z'),('Z','Z','B')]
COLS=[(),('B',),('T','T'),('T','T','T'),('B','B')]
D=4

def record(S,b):
    h=ind.size(S);T=list(S)
    for _ in range(b-1):T.append('Z' if h==0 else 'B' if h==1 else 'T');h+=1
    return tuple(T)
@lru_cache(None)
def count(S,m):
    if not S and not m:return 1
    total=sum(count(record(S,b),m-b) for b in range(1,m+1))
    for k in range(ind.size(S)):
        T=ind.delete_formula(S,k)
        if T is not None:total+=count(T,m)
    return total

def mul(a,b):return [sum(a[j]*b[i-j] for j in range(i+1)) for i in range(D+1)]
def determinant(A):
    out=[0]*(D+1)
    for p in permutations(range(len(A))):
        sign=(-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
        term=[1]+[0]*D
        for i,j in enumerate(p):term=mul(term,A[i][j])
        out=[a+sign*b for a,b in zip(out,term)]
    return out

def rank(A,p=1000000007):
    A=[[v%p for v in row] for row in A];r=0
    for j in range(len(A[0])):
        k=next((i for i in range(r,len(A)) if A[i][j]),None)
        if k is None:continue
        A[r],A[k]=A[k],A[r];v=pow(A[r][j],p-2,p);A[r]=[x*v%p for x in A[r]]
        for i in range(r+1,len(A)):
            v=A[i][j]
            if v:A[i]=[(a-v*b)%p for a,b in zip(A[i],A[r])]
        r+=1
        if r==len(A):break
    return r

def apply(code):
    S=()
    for tag,k in code:S=record(S,k) if tag=='N' else ind.delete_formula(S,k-1)
    return S

def main():
    start=time.monotonic()

    A=[[[count(P+W,m) for m in range(D+1)] for W in COLS] for P in ROWS]
    det=determinant(A);assert det==[0,0,0,0,-41472]
    fixture=Path(__file__).resolve().parent/'author-rank-five-coefficients.json'
    author=json.loads(fixture.read_text());assert A==author['matrix_entry_coefficients'];assert det==author['determinant_coefficients']
    block=[[A[a][b][i-j] if i>=j else 0 for j in range(D+1) for b in range(5)] for i in range(D+1) for a in range(5)]
    r=rank(block);assert r==21
    seed=[('N',6),('H',1),('H',1),('H',2)]
    codes=[[('N',3)],[('N',5),('H',3)],[('N',4)],seed,seed+[('N',3),('H',3)]]
    assert [apply(code) for code in codes]==ROWS
    # Concrete semantic closure obligations already appear from the fixed context.
    assert ind.delete_formula(('Z','Z','T','T'),0)==('Z','O','B')
    assert ind.delete_formula(('Z','Z','T','B'),1)==('Z',2)
    out={'status':'EXACT rank>=5 obstruction for the common fixed/free context family','scope':'Does not disprove rank4 of the narrower ZB-only family','row_initial_states':ROWS,'row_reachability_codes':codes,'column_words':COLS,'degree_bound':D,'matrix_entry_coefficients':A,'determinant_coefficients':det,'toeplitz_modular_certificate':{'prime':1000000007,'dimension':25,'rank':r,'four_dimensional_upper_bound':20},'closure_witnesses':[{'initial':['Z','Z','T','T'],'delete_rank':1,'result':['Z','O','B']},{'initial':['Z','Z','T','B'],'delete_rank':2,'result':['Z',2]}],'memo_states':count.cache_info().currsize,'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'independent_transition_sha256':hashlib.sha256(Path(ind.__file__).read_bytes()).hexdigest(),'author_fixture_sha256':hashlib.sha256(fixture.read_bytes()).hexdigest()}
    Path('independent-minor-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=="__main__":main()
