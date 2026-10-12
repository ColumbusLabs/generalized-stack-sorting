"""Candidate exact (3,3) lazy-state normal form, proved in normal-form-draft.md.

An atom is 'Z','O','B','T', or integer m>=2 for C_m. None is rejection;
() denotes the empty-word language. Transitions take set images, never history
multiplicities. This research module does not claim an algebraicity theorem.
"""
from itertools import product
from collections import defaultdict
from functools import lru_cache

UNARY={'Z':(0,), 'O':(1,), 'B':(0,1), 'T':(0,1,2)}

def height(state):
    return sum(a if type(a) is int else 1 for a in state)

def cat(prefix, suffix):
    return None if suffix is None else tuple(prefix)+suffix

def clause(m):
    if m==0:return None
    if m==1:return ('Z',)
    if m>=2:return (m,)
    raise ValueError(m)

def exceptional(state):
    """Return (t,A) for a nonempty T^t A unary tail, else None."""
    if state and state[-1] in UNARY and all(a=='T' for a in state[:-1]):
        return len(state)-1,state[-1]
    return None

@lru_cache(None)
def f1(state):
    if not state:return ()
    tail=exceptional(state)
    if tail is None:return None
    t,a=tail
    return ('O',)*t+({'Z':'Z','O':'O','B':'B','T':'B'}[a],)

@lru_cache(None)
def f0(state):
    """Iterative form of the proved recursion; no height/recursion-depth cap."""
    if not state:return ()
    n=len(state)
    # A suffix is exceptional exactly when it begins at or beyond exc_start.
    # This avoids repeatedly rescanning every suffix of a long state.
    exc_start=n
    if state[-1] in UNARY:
        exc_start=n-1
        while exc_start>0 and state[exc_start-1]=='T':exc_start-=1
    out=[];i=0
    while i<n:
        if i>=exc_start:
            t=n-i-1;a=state[-1]
            if a=='Z':suffix=('B',)*t+('Z',)
            elif a in ('O','B'):suffix=clause(t+1)
            else:suffix=('B',)*(t+1)
            return tuple(out)+suffix
        a=state[i]
        if a=='Z':return cat(tuple(out)+('Z',),f1(state[i+1:]))
        if a=='O':out.append('Z');i+=1;continue
        if a=='B':
            out.append('Z');i+=1
            if i>=exc_start:
                t=n-i-1;last=state[-1]
                suffix=('B',)*t+('Z',) if last=='Z' else ('B',)*(t+1)
                return tuple(out)+suffix
            continue
        if a=='T':out.append('B');i+=1;continue
        if i+1==n:return tuple(out)+('Z',)*(a-1)+('B',)
        return cat(tuple(out)+('Z',)*a,f1(state[i+1:]))
    return tuple(out)

@lru_cache(None)
def union01(state):
    if not state:return ()
    tail=exceptional(state)
    if tail is None:return f0(state)
    t,a=tail
    return ('B',)*t+('Z',) if a=='Z' else ('B',)*(t+1)

def push(state):
    if state is None:return None
    h=height(state)
    return state+('Z' if h==0 else 'B' if h==1 else 'T',)

def record(state,b):
    if type(b) is not int or b<1:raise ValueError('positive record jump required')
    for _ in range(b-1):state=push(state)
    return state

def pop(state,k):
    if state is None:return None
    h=height(state)
    if type(k) is not int or not 1<=k<=h:raise ValueError('held rank out of range')
    off=k-1
    for i,a in enumerate(state):
        size=a if type(a) is int else 1
        if off<size:break
        off-=size
    p,w=state[:i],state[i+1:]
    if type(a) is str:
        if not w:return p
        suffix=f0(w) if a=='Z' else f1(w) if a=='O' else union01(w)
        return cat(p,suffix)
    ell,r=off,a-off-1
    if r>=2 or r>=1 and w:
        return cat(p+('B',)*ell,f0(('B',)*r+w))
    if r==1:return cat(p,clause(ell+1))
    if not w:return p+('B',)*ell
    tail=exceptional(w)
    if tail is not None and tail[1] in ('O','B'):
        return cat(p,clause(ell+tail[0]+1))
    return cat(p+('B',)*ell,f0(w))

def expand(state):
    if state is None:return frozenset()
    words={()}
    for a in state:
        factors=((d,) for d in UNARY[a]) if type(a) is str else (b for b in product((0,1),repeat=a) if 0 in b)
        factors=tuple(factors)
        words={p+w for p in words for w in factors}
    return frozenset(words)

def encode(order):
    return tuple(sum(v<j for v in order[:order.index(j)]) for j in range(1,len(order)+1))

def decode(code):
    out=[]
    for j,a in enumerate(code,1):out.insert(a,j)
    return tuple(out)

def generated_member(permutation):
    if sorted(permutation)!=list(range(1,len(permutation)+1)):
        raise ValueError('permutation required')
    state=();held=[];maximum=0
    for value in permutation:
        if value>maximum:
            b=value-maximum
            state=record(state,b)
            held.extend(range(maximum+1,value))
            maximum=value
        else:
            k=held.index(value)
            state=pop(state,k+1)
            if state is None:return False
            held.pop(k)
    return state==()

def counts_through(max_n):
    """Distinct generated permutations by unique output codes; bounded test DP."""
    answers=[];peak_states=[]
    for n in range(max_n+1):
        layer={():1};peak=1
        for outputs in range(n):
            nxt=defaultdict(int)
            for state,count in layer.items():
                h=height(state)
                for b in range(1,n-outputs-h+1):
                    nxt[record(state,b)]+=count
                for k in range(1,h+1):
                    target=pop(state,k)
                    if target is not None:nxt[target]+=count
            layer=nxt;peak=max(peak,len(layer))
        answers.append(layer.get((),0));peak_states.append(peak)
    return answers,peak_states
