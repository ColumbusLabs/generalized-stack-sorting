#!/usr/bin/env python3
"""Independent finite challenge of unary/C_m normal form, using literal stacks.

Standard library only. This is finite evidence, not an all-length proof.
"""
from itertools import product
from functools import lru_cache
import argparse, hashlib, json, os, random, resource, time, sys
from pathlib import Path
REPO_ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(REPO_ROOT/"src"))
from stack_sorting import three_push as candidate

UNARY={'Z':(0,), 'O':(1,), 'B':(0,1), 'T':(0,1,2)}

def size(R): return sum(1 if isinstance(x,str) else x for x in R)
def C(n): return None if n==0 else ('Z',) if n==1 else (n,)
def cat(A,B): return None if A is None or B is None else A+B

@lru_cache(None)
def factor(F):
    return tuple((a,) for a in UNARY[F]) if isinstance(F,str) else tuple(w for w in product((0,1),repeat=F) if 0 in w)

def expand(R):
    if R is None:return frozenset()
    return frozenset(sum(ws,()) for ws in product(*(factor(F) for F in R)))

def grammar(n):
    if not n: yield ();return
    for F in UNARY:
        for rest in grammar(n-1):yield (F,)+rest
    for m in range(2,n+1):
        for rest in grammar(n-m):yield (m,)+rest

def is_special(W):
    return bool(W) and W[-1] in ('O','B') and all(F=='T' for F in W[:-1])

def f1(W):
    if not W:return ()
    if any(F!='T' for F in W[:-1]) or W[-1] not in UNARY:return None
    return ('O',)*(len(W)-1)+({'Z':'Z','O':'O','B':'B','T':'B'}[W[-1]],)

def f0(W):
    if not W:return ()
    F,rest=W[0],W[1:]
    if F=='Z':return cat(('Z',),f1(rest))
    if F=='O':return cat(('Z',),f0(rest))
    if F=='B':return cat(('Z',),f01(rest))
    if F=='T':return C(size(rest)+1) if is_special(rest) else cat(('B',),f0(rest))
    return ('Z',)*(F-1)+('B',) if not rest else cat(('Z',)*F,f1(rest))

def f01(W):
    return ('B',)*size(W) if is_special(W) else f0(W)

def delete_formula(R,k):
    """Zero-indexed coordinate, representing one held-value deletion."""
    left=()
    for i,F in enumerate(R):
        m=1 if isinstance(F,str) else F
        if k>=m:
            k-=m;left+=(F,);continue
        W=R[i+1:]
        if isinstance(F,str):
            tail=f0(W) if F=='Z' else f1(W) if F=='O' else f01(W)
        else:
            ell,r=k,m-k-1
            if r>=2 or (r>=1 and W):tail=cat(('B',)*ell,f0(('B',)*r+W))
            elif r==1:tail=C(ell+1)
            elif not W:tail=('B',)*ell
            elif is_special(W):tail=C(ell+size(W))
            else:tail=cat(('B',)*ell,f0(W))
        return cat(left,tail)
    raise ValueError('coordinate out of range')

def transduce(word,p):
    out=[]
    for a in word:
        if a<=p:out.append(a);p+=1
        else:out.append(a-1)
        if p>=3:return None
    return tuple(out)

def decode(c):
    stack=[]
    for value,slot in enumerate(c,1):
        assert 0<=slot<value
        stack.insert(slot,value)
    return tuple(stack)

def encode(stack):
    return tuple(sum(v<j for v in stack[:stack.index(j)]) for j in range(1,len(stack)+1))

def literal_delete(c,k):
    stack=decode(c)
    if stack.index(k)>2:return None
    return encode(tuple(x-(x>k) for x in stack if x!=k))

def canonical(L):
    """Factor via independent cuts, without consulting the proposed deletion."""
    if not L:return None
    n=len(next(iter(L)))
    if not n:return ()
    for j in range(1,n):
        A=frozenset(w[:j] for w in L);B=frozenset(w[j:] for w in L)
        if len(L)==len(A)*len(B):return canonical(A)+canonical(B)
    if n==1:
        U=tuple(sorted(w[0] for w in L))
        return (next(F for F,vals in UNARY.items() if U==vals),)
    if L==frozenset(factor(n)):return (n,)
    raise AssertionError(('noncandidate prime',sorted(L)))

def check(R,stats):
    L=expand(R)
    assert canonical(L)==R
    stats['languages']+=1
    for k in range(1,size(R)+1):
        actual=set()
        for c in L:
            a=literal_delete(c,k)
            b=transduce(c[k:],c[k-1])
            if b is not None:b=c[:k-1]+b
            assert a==b, ('transducer mismatch',R,k,c,a,b)
            if a is not None:actual.add(a)
            stats['literal_stack_cases']+=1
        actual=frozenset(actual)
        predicted=delete_formula(R,k-1)
        assert candidate.pop(R,k)==predicted, ('implementation mismatch',R,k,predicted,candidate.pop(R,k))
        assert actual==expand(predicted), ('formula mismatch',R,k,predicted,sorted(actual))
        assert canonical(actual)==predicted
        stats['deletions']+=1


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-length',type=int,default=8);ap.add_argument('--random-trials',type=int,default=1000);ap.add_argument('--out',default='independent-results.json');args=ap.parse_args()
    start=time.monotonic();stats={'status':'PASS','max_length':args.max_length,'languages':0,'deletions':0,'literal_stack_cases':0,'suffix_languages':0,'random_trials':args.random_trials,'seed':109033,'per_length':[]}
    for n in range(1,args.max_length+1):
        before=stats['languages']
        for R in grammar(n-1):
            if R and R[0]=='T':continue
            check(('Z',)+R,stats)
        stats['per_length'].append({'length':n,'languages':stats['languages']-before,'cumulative_deletions':stats['deletions']})
        print(json.dumps(stats['per_length'][-1]),flush=True)
    # Arbitrary products, with no ambient restrictions, challenge the suffix lemmas.
    for n in range(args.max_length):
        for R in grammar(n):
            L=expand(R)
            for p,formula in ((0,f0),(1,f1)):
                image=frozenset(t for c in L if (t:=transduce(c,p)) is not None)
                assert (candidate.f0 if p==0 else candidate.f1)(R)==formula(R)
                assert image==expand(formula(R)),('suffix',R,p,formula(R),image)
            stats['suffix_languages']+=1
    rng=random.Random(stats['seed']);done=0
    while done<args.random_trials:
        R=('Z',);n=rng.randrange(9,31)
        while size(R)<n:
            remaining=n-size(R)
            F=rng.choice(['Z','Z','O','O','B','T']+list(range(2,min(remaining,10)+1)))
            if size(R)==1 and F=='T':continue
            R+=(F,)
        if size(R)!=n:continue
        estimated=1
        for F in R:estimated*=len(factor(F))
        if estimated>5000:continue
        check(R,stats);done+=1
    stats['seconds']=time.monotonic()-start
    stats['peak_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    stats['candidate_sha256']=hashlib.sha256(open(candidate.__file__,'rb').read()).hexdigest()
    stats['source_sha256']=hashlib.sha256(open(__file__,'rb').read()).hexdigest()
    with open(args.out,'w') as f:json.dump(stats,f,indent=2);f.write('\n')
    print(json.dumps(stats,indent=2))
if __name__=='__main__':main()
