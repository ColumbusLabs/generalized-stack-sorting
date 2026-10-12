"""Small exact check of four-control first-return equations; no model imports."""
from pathlib import Path
import argparse, hashlib, json, resource, time
Q=4

def zero(): return [[0]*Q for _ in range(Q)]
def eye(): return [[int(i==j) for j in range(Q)] for i in range(Q)]
def add(a,b): return [[a[i][j]+b[i][j] for j in range(Q)] for i in range(Q)]
def scale(a,v): return [[v*t for t in row] for row in a]
def mul(a,b):
    c=zero()
    for i in range(Q):
        for k in range(Q):
            if a[i][k]:
                for j in range(Q): c[i][j]+=a[i][k]*b[k][j]
    return c

def conv(a,b,d):
    r=zero()
    for k in range(d+1): r=add(r,mul(a[k],b[d-k]))
    return r

def counts(N):
    """Exact four-control recurrence, with explicit bounded prototype admission."""
    if type(N) is not int or not 0 <= N <= 26:
        raise ValueError("This bounded prototype accepts integer N in 0..26")
    # X[a][d] is coefficient x^d of first-return matrix for block a.
    A=N+2
    X=[[zero() for d in range(N+1)] for a in range(A+1)]
    X[0][0]=eye()
    X[1][0][0][1]=1
    X[1][0][1][3]=1
    X[2][0][0][2]=1
    for n in range(1,N+1):
        # B[a] = sum_{m+j=a-1} X[1]^m X[j], the t=1 and t=2 drain sum.
        B=[[zero() for d in range(n)] for a in range(A+1)]
        for a in range(1,A+1):
            for d in range(n):
                B[a][d]=add(conv(X[1],B[a-1],d),X[a-1][d])
        XX=[conv(X[1],X[1],d) for d in range(n)]
        tail=zero()
        for a in range(A,0,-1):
            tail=add(tail,X[a][n-1])
            if a==1: D3=eye() if n==1 else zero()
            elif a==2: D3=scale(X[1][n-1],2)
            else: D3=add(scale(X[a-1][n-1],2),conv(X[2],B[a-2],n-1))
            X[a][n][0]=add(tail,D3)[0]
            X[a][n][1]=conv(X[1],B[a],n-1)[0]
            X[a][n][2]=conv(X[2],B[a],n-1)[0]
            X[a][n][3]=conv(XX,B[a],n-1)[0]
    # F=1/(1-x(1+sum_a X[a][0,0])).
    atom=[0]*(N+1)
    if N: atom[1]=1
    for d in range(1,N+1): atom[d]+=sum(X[a][d-1][0][0] for a in range(1,A+1))
    F=[1]+[0]*N
    for n in range(1,N+1): F[n]=sum(atom[j]*F[n-j] for j in range(1,n+1))
    violations=[]
    sizes=[0,1,2,2]
    for a in range(1,A+1):
        for d in range(N+1):
            for p in range(Q):
                for q in range(Q):
                    if d<a+sizes[p]-sizes[q] and X[a][d][p][q]: violations.append((a,d,p,q))
    return F,violations

def run_check(max_n, reference_counts=None):
    start=time.perf_counter()
    seq,bad=counts(max_n)
    result={
        "scope":"exact first-return recurrence check; finite computation is not the proof",
        "max_n":max_n,"counts":seq,"valuation_bound_violations":bad,
        "seconds":time.perf_counter()-start,
        "max_rss_kib":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "algorithm_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    if reference_counts is not None:
        path=Path(reference_counts)
        raw=path.read_bytes()
        ref=json.loads(raw)
        old=ref["counts"]
        if len(old)<max_n+1:
            raise ValueError("Reference has too few coefficients for this comparison")
        result["reference_sha256"]=hashlib.sha256(raw).hexdigest()
        result["reference_source_revision"]=ref.get("source_revision")
        result["agrees_with_existing_exact_code_dp"]=seq==old[:max_n+1]
    if bad or result.get("agrees_with_existing_exact_code_dp") is False:
        raise AssertionError(result)
    return result

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--max-n",type=int,default=12)
    ap.add_argument("--reference-counts",type=Path)
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    if not 0<=args.max_n<=16:
        ap.error("Small routine probe bound is 0..16; use compare_existing_26.py for the fixed n26 check")
    result=run_check(args.max_n,args.reference_counts)
    encoded=json.dumps(result,indent=2)+"\n"
    if args.output is not None: args.output.write_text(encoded)
    print(encoded,end="")
