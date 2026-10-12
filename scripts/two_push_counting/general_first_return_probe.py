"""Bounded general-(2,s) first-return recurrence check, using standard library."""
from pathlib import Path
import argparse,hashlib,json,resource,sys,time

def compositions(n):
    if not n:
        yield ()
    else:
        for a in range(1,n+1):
            for tail in compositions(n-a): yield (a,)+tail

def first_return_counts(s,N):
    if type(s) is not int or not 2<=s<=4 or type(N) is not int or not 0<=N<=8:
        raise ValueError('This small validation supports only s=2..4 and N=0..8')
    controls=[c for h in range(s) for c in compositions(h)]
    idx={c:i for i,c in enumerate(controls)}
    d=len(controls); A=N+s-1
    def zero(): return [[0]*d for _ in range(d)]
    def eye(): return [[int(i==j) for j in range(d)] for i in range(d)]
    def add(a,b): return [[a[i][j]+b[i][j] for j in range(d)] for i in range(d)]
    def scale(a,v): return [[v*y for y in row] for row in a]
    def mul(a,b):
        c=zero()
        for i in range(d):
            for k in range(d):
                if a[i][k]:
                    for j in range(d): c[i][j]+=a[i][k]*b[k][j]
        return c
    def conv(a,b,n):
        c=zero()
        for k in range(n+1): c=add(c,mul(a[k],b[n-k]))
        return c
    X=[[zero() for n in range(N+1)] for a in range(A+1)]
    X[0][0]=eye()
    for a in range(1,min(s,A+1)):
        for p,c in enumerate(controls):
            if sum(c)+a<s: X[a][0][p][idx[c+(a,)]]=1
    for n in range(1,N+1):
        B=[[zero() for k in range(n)] for a in range(A+1)]
        for a in range(1,A+1):
            for k in range(n): B[a][k]=add(conv(X[1],B[a-1],k),X[a-1][k])
        W={():[eye()]+[zero() for _ in range(n-1)]}
        for c in controls[1:]: W[c]=[conv(W[c[:-1]],X[c[-1]],k) for k in range(n)]
        D={}
        for t in range(1,s+1):
            for a in range(1,A+1):
                if a<t: D[t,a]=[scale(X[a-1][k],a) for k in range(n)]
                else: D[t,a]=[add(scale(X[a-1][k],t-1),conv(X[t-1],B[a-t+1],k)) for k in range(n)]
        tail=zero()
        for a in range(A,0,-1):
            tail=add(tail,X[a][n-1])
            for p,c in enumerate(controls):
                row=conv(W[c],D[s-sum(c),a],n-1)[0]
                if not c: row=[row[j]+tail[0][j] for j in range(d)]
                X[a][n][p]=row
    atom=[0]*(N+1)
    if N: atom[1]=1
    for n in range(1,N+1): atom[n]+=sum(X[a][n-1][0][0] for a in range(1,A+1))
    F=[1]+[0]*N
    for n in range(1,N+1): F[n]=sum(atom[j]*F[n-j] for j in range(1,n+1))
    violations=[]
    for a in range(1,A+1):
        for n in range(N+1):
            for p,c in enumerate(controls):
                for q,e in enumerate(controls):
                    if n<a+sum(c)-sum(e) and X[a][n][p][q]: violations.append((a,n,p,q))
    return F,violations,d

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--source-root',type=Path,required=True,help='Repository src folder for independent composition-DP reference')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    sys.path.insert(0,str(args.source_root))
    from stack_sorting.two_push import permutation_counts
    out=[]
    for s in (2,3,4):
        start=time.perf_counter(); seq,bad,d=first_return_counts(s,8)
        elapsed=time.perf_counter()-start
        ref=permutation_counts(s,8,state_limit=100000)
        assert not bad and seq==ref
        out.append({'s':s,'control_count':d,'max_n':8,'counts':seq,'agrees_with_composition_dp':seq==ref,'valuation_bound_violations':bad,'first_return_seconds':elapsed})
    result={'scope':'small recurrence checks for s=2,3,4; not a proof of the all-s theorem','results':out,'algorithm_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'reference_algorithm_sha256':hashlib.sha256((args.source_root/'stack_sorting'/'two_push.py').read_bytes()).hexdigest(),'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    args.output.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2))
