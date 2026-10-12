"""Bounded necessary-condition experiment, never a finite-rank upper bound."""
import argparse,sys,json,time,resource,hashlib
from pathlib import Path
from functools import lru_cache
from itertools import product
BASE=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(BASE/'src'))
from stack_sorting import three_push as nf

@lru_cache(None)
def count(S,m):
 if not S and not m:return 1
 ans=0
 for b in range(1,m+1):ans+=count(nf.record(S,b),m-b)
 for k in range(1,nf.height(S)+1):
  T=nf.pop(S,k)
  if T is not None:ans+=count(T,m)
 return ans

def rank(A,p=1000000007):
 A=[[x%p for x in row] for row in A];r=0;cols=[]
 for j in range(len(A[0])):
  k=next((i for i in range(r,len(A)) if A[i][j]),None)
  if k is None:continue
  A[r],A[k]=A[k],A[r];inv=pow(A[r][j],p-2,p);A[r]=[x*inv%p for x in A[r]]
  for i in range(r+1,len(A)):
   v=A[i][j]
   if v:A[i]=[(a-v*b)%p for a,b in zip(A[i],A[r])]
  cols.append(j);r+=1
  if r==len(A):break
 return r

if __name__ == '__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--degree',type=int,default=4);ap.add_argument('--words',type=int,default=2);ap.add_argument('--alphabet',default='BTZ');ap.add_argument('--out',required=True);args=ap.parse_args()
 start=time.monotonic();chunks={'B':('B',),'T':('T',),'Z':('Z',),'O':('Z','O'),'C':(2,),'D':(3,),'E':(4,)}
 words=[w for n in range(args.words+1) for w in product(args.alphabet,repeat=n)]
 expanded=[sum((chunks[c] for c in w),()) for w in words];L=len(words);D=args.degree
 C=[[[count(('Z','B')+u+v,m) for m in range(D+1)] for v in expanded] for u in expanded]
 print('entries done',L,count.cache_info(),time.monotonic()-start,flush=True)
 rows=[]
 for m in range(D+1):
  A=[[C[a][b][i-j] if i>=j else 0 for j in range(m+1) for b in range(L)] for i in range(m+1) for a in range(L)]
  r=rank(A);row={'degree':m,'dimension':len(A),'rank_mod':r,'finite_rank_lower_bound':(r+m)//(m+1)};rows.append(row);print(row,flush=True)
 out={'scope':'Lower bounds only for full completion-count Hankel rank over expanded factor chunk words; no rank upper bound or equation proof.','prefix':['Z','B'],'alphabet':args.alphabet,'chunks':chunks,'words':words,'expanded_words':expanded,'degree':D,'coefficients':C,'ranks':rows,'cache':count.cache_info()._asdict(),'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'normal_form_sha256':hashlib.sha256((BASE/'src/stack_sorting/three_push.py').read_bytes()).hexdigest()}
 Path(args.out).write_text(json.dumps(out,indent=2)+'\n')
