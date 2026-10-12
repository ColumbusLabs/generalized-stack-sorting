#!/usr/bin/env python3
"""Bounded exact polynomial replay; no completion-count oracle in this check."""
import sys, json, resource, hashlib
from itertools import product
from collections import Counter
from functools import lru_cache
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2))
BASE=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(BASE/'src'))
from stack_sorting.three_push import f0, union01

def clean(p):return {w:c for w,c in p.items() if c}
def add(*polys):
    out=Counter()
    for p in polys:
        for w,c in p.items():out[w]+=c
    return clean(out)
def pre(a,p):return {(a,)+w:c for w,c in p.items()}
def lam(p):return add(pre('B',p),{('Z',)+w:-c for w,c in p.items()})
ONE={():1};ZERO={}
@lru_cache(None)
def channels(w):
    if not w:return ONE,ONE,ZERO,ONE
    a=w[0];F,J,K,E=channels(w[1:])
    if a=='Z':return pre('Z',J),pre('Z',E),ZERO,ZERO
    if a=='B':return pre('Z',add(F,K)),pre('B',E),lam(E),ZERO
    return add(pre('B',F),pre('Z',K)),add(pre('Z',J),lam(E)),lam(K),ZERO

def reduce_nf(s):
    if s is None:return ZERO
    out=ONE
    for a in s:
        if type(a) is str:
            a='Z' if a=='O' else a
            out={w+(a,):c for w,c in out.items()}
        else:
            new=Counter()
            for w,c in out.items():
                for tail in product(('B','Z'),repeat=a):
                    if all(b=='B' for b in tail):continue
                    new[w+tail]+=c*((-1)**(tail.count('Z')+1))
            out=clean(new)
    return out

count=0
for h in range(10):
    for w in product('ZBT',repeat=h):
        F,J,K,E=channels(w)
        assert F==reduce_nf(f0(w)),('F',w,F,reduce_nf(f0(w)))
        assert add(F,K)==reduce_nf(union01(w)),('U',w)
        count+=1
    channels.cache_clear()
    f0.cache_clear();union01.cache_clear()
result={'scope':'Finite exact noncommutative-polynomial check of the compact signed suffix transducer against the reviewed normal-form functions after formal O-run/clause substitutions; not an all-length proof or a finite-rank certificate.','word_lengths':[0,9],'suffix_words':count,'operator_equalities':2*count,'status':'PASS','normal_form_sha256':hashlib.sha256((BASE/'src/stack_sorting/three_push.py').read_bytes()).hexdigest()}
print(json.dumps(result,indent=2))
Path(__file__).with_name('signed-suffix-transducer-checks.json').write_text(json.dumps(result,indent=2)+'\n')
