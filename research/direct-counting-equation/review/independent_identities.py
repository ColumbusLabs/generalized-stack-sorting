#!/usr/bin/env python3
"""Rebuild the scalar lift from reviewed rational equations; no producer imports."""
from pathlib import Path
import os, sys, json, hashlib, time, resource
import sympy as S
from flint import fmpq, fmpq_mpoly, fmpq_mpoly_ctx
resource.setrlimit(resource.RLIMIT_AS, (640<<20,640<<20))
resource.setrlimit(resource.RLIMIT_CPU, (150,150))
start=time.monotonic(); ROOT=Path(__file__).resolve().parent
for name,row in json.loads((ROOT/'input_manifest.json').read_text()).items():
    assert hashlib.sha256((ROOT/'frozen'/name).read_bytes()).hexdigest()==row['sha256'], name
def read(name): return json.loads((ROOT/'frozen'/name).read_text())
a,t,u,i,q,g,s,c,o,p,x,Y=S.symbols('a t u i q g s c o p x Y')
parse=lambda v:S.sympify(v,locals={str(z):z for z in (a,t,u,i,q,g,s,c,o,p,x,Y)})
rat=lambda row:parse(row['numerator'])/parse(row['denominator'])
five=read('five_scalar_reduction.json'); changed=read('changed_scalar_coordinates.json')['equations']
coord={g:u/(q*t),s:t/q,o:i-a}
cs=S.cancel(parse(five['c_elimination']['answer']).subs(coord,simultaneous=True))
v2=parse(read('eight_parameter_beta_elimination.json')['beta_over_beta0']['beta2'])
v2=S.cancel(v2.subs(p,-i*q).subs(coord,simultaneous=True).subs(c,cs))
G=S.cancel(1+x+2*x*x/(1-x*v2))
print('Rebuilt c, beta2/beta0, and G from accepted source identities',flush=True)
ctx=fmpq_mpoly_ctx.get(['Y','x']); YY,xx=ctx.gens()
cand=read('scalar_G_degree12_x6_candidate.json')
P=ctx.from_dict({(k,j):fmpq(co) for j,k,co in cand['terms']})
assert len(P.to_dict())==69 and P.degrees()==(12,6)
assert len(set((j,k) for j,k,co in cand['terms']))==69
maps=read('parameter_map_candidates_exact.json')['maps']
names=['a','t','u','i','q']; vs=[a,t,u,i,q]
fracs={name:(fmpq_mpoly(maps[name]['numerator'].replace('**','^'),ctx),fmpq_mpoly(maps[name]['denominator'].replace('**','^'),ctx)) for name in names}
equations={name:parse(row['numerator']) for name,row in changed.items()}
gn,gd=S.fraction(G);equations['independently_derived_G']=Y*gd-gn
proofs={};quots={}
def homogenize(expr):
    sp=S.Poly(expr,*vs,x,Y); ds=sp.degree_list()
    # One common denominator per coordinate, computed independently from monomials.
    cache={name:([fracs[name][0]**k for k in range(ds[j]+1)],
                 [fracs[name][1]**k for k in range(ds[j]+1)]) for j,name in enumerate(names)}
    ans=ctx.constant(0)
    for mon,co in sp.terms():
        z=ctx.constant(fmpq(str(co)))*xx**mon[-2]*YY**mon[-1]
        for j,name in enumerate(names):
            np,dp=cache[name];z*=np[mon[j]]*dp[ds[j]-mon[j]]
        ans+=z
    return ans,ds
for name,expr in equations.items():
    value,degrees=homogenize(expr); quotient,remainder=divmod(value,P)
    assert not remainder, name
    assert quotient*P==value, name+' quotient identity'
    proofs[name]={'source_degrees':list(map(int,degrees)),'source_terms':len(S.Poly(expr,*vs,x,Y).terms()),'substituted_terms':len(value.to_dict()),'quotient_terms':len(quotient.to_dict()),'quotient_degrees':list(map(int,quotient.degrees())),'exact_identity':True}
    quots[name]=str(quotient)
    print(name,proofs[name],flush=True)
# Two mutations are rejected by exact nonzero remainder, not by source-hash guards.
wrong=ctx.from_dict({(0,0):fmpq(1)})+P
last,_=homogenize(equations['independently_derived_G'])
assert divmod(last,wrong)[1]
old=fracs['a'];fracs['a']=(-old[0],old[1])
bad,_=homogenize(equations['short4']);assert divmod(bad,P)[1]
fracs['a']=old
derived={'c':str(cs),'v2':str(v2),'G':str(G)}
(ROOT/'independent_derived_formulas.json').write_text(json.dumps(derived,indent=2)+'\n')
(ROOT/'division_quotients.json').write_text(json.dumps(quots,indent=2)+'\n')
receipt={'status':'PASS','identities':proofs,'negative_controls':['constant coefficient of P changed by 1','a numerator sign reversed'],'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'identities_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2),flush=True)
