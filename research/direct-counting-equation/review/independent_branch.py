#!/usr/bin/env python3
"""Construct the scalar root by a simple-root recurrence and prove regular lifting."""
from pathlib import Path
import sys,json,hashlib,time,resource
import sympy as S
from flint import fmpq, fmpq_poly, fmpq_mpoly_ctx, fmpq_mpoly
resource.setrlimit(resource.RLIMIT_AS,(640<<20,640<<20))
resource.setrlimit(resource.RLIMIT_CPU,(150,150))
ROOT=Path(__file__).resolve().parent;start=time.monotonic()
for name,row in json.loads((ROOT/'input_manifest.json').read_text()).items():
    assert hashlib.sha256((ROOT/'frozen'/name).read_bytes()).hexdigest()==row['sha256'],name
read=lambda name:json.loads((ROOT/'frozen'/name).read_text())
ctx=fmpq_mpoly_ctx.get(['z','x']);z,x=ctx.gens()
terms=read('scalar_G_degree12_x6_candidate.json')['terms']
P=ctx.from_dict({(j,k):fmpq(co) for k,j,co in terms})
C8=[1,1,2,6,24,120,720,5004,38844]
C=sum((co*x**k for k,co in enumerate(C8)),ctx.constant(0))
# Independent sparse substitution, exact x-adic division, and a full identity.
subst=sum((co*x**k*(C+x**9*z)**j for k,j,co in terms),ctx.constant(0))
valuation=int(min(mon[1] for mon in subst.to_dict()))
assert valuation==20
H=ctx.from_dict({(j,k-20):co for (j,k),co in subst.to_dict().items()})
assert H*x**20==subst
base=ctx.from_dict({mon:co for mon,co in H.to_dict().items() if mon[1]==0})
assert base==-16*(z-325692)*(z-325656)
assert H.derivative(0)(325692,0)==-576
# Coefficients of the unique simple root H(z(x),x)=0; no fitted series imported.
def coefficient_rows(poly):
    d=poly.degrees()[0]
    return [fmpq_poly([poly.to_dict().get((j,k),0) for k in range(poly.degrees()[1]+1)]) for j in range(d+1)]
hrows=coefficient_rows(H)
def horner(rows,v,N):
    out=fmpq_poly([])
    for row in rows[::-1]:out=((out*v).truncate(N)+row).truncate(N)
    return out
NZ=32;coeff=[fmpq(325692)]
assert not horner(hrows,fmpq_poly(coeff),1)
for degree in range(1,NZ):
    residual=horner(hrows,fmpq_poly(coeff),degree+1)
    assert all(residual[j]==0 for j in range(degree))
    coeff.append(residual[degree]/576)
    assert not horner(hrows,fmpq_poly(coeff),degree+1)
N=NZ+9;G=fmpq_poly(C8+[0]*(N-len(C8)))+fmpq_poly([0]*9+coeff)
assert not horner(coefficient_rows(P),G,N)
print('Simple scalar branch and recurrence PASS; certified G precision',N,flush=True)

a,t,u,i,q,g,s,c,o,p,xx,YY=S.symbols('a t u i q g s c o p x Y')
loc={str(v):v for v in (a,t,u,i,q,g,s,c,o,p,xx,YY)}
parse=lambda text:S.sympify(text,locals=loc)
def evaluate_poly(expr,values,precision):
    pol=S.Poly(expr,*values);out=fmpq_poly([])
    powers={v:[fmpq_poly([1])] for v in values}
    for v,d in zip(values,pol.degree_list()):
        for k in range(int(d)):powers[v].append((powers[v][-1]*values[v]).truncate(precision))
    for mon,co in pol.terms():
        term=fmpq_poly([fmpq(str(co))])
        for v,k in zip(values,mon):term=(term*powers[v][k]).truncate(precision)
        out+=term
    return out.truncate(precision)
def val(poly,N):return next((k for k in range(N) if poly[k]),None)
ledger={}
def divide(nn,dd,N,label):
    vn,vd=val(nn,N),val(dd,N);assert vd is not None,(label,'denominator not certified nonzero')
    assert vn is None or vn>=vd,(label,'pole',vn,vd)
    size=N-vd;lead=dd[vd];out=[]
    for k in range(size):out.append((nn[k+vd]-sum(dd[j+vd]*out[k-j] for j in range(1,k+1)))/lead)
    ans=fmpq_poly(out)
    assert (ans*dd-nn).truncate(N)==0
    ledger[label]={'numerator_valuation':vn,'denominator_valuation':vd,'denominator_leading':str(lead),'certified_modulus':size}
    return ans,size
maps=read('parameter_map_candidates_exact.json')['maps'];values={xx:fmpq_poly([0,1])};precisions={xx:N}
for v in (a,t,u,i,q):
    entry=maps[str(v)];nv=evaluate_poly(parse(entry['numerator']),{YY:G,xx:values[xx]},N);dv=evaluate_poly(parse(entry['denominator']),{YY:G,xx:values[xx]},N)
    values[v],precisions[v]=divide(nv,dv,N,'map_'+str(v))
M=min(precisions.values());values={v:row.truncate(M) for v,row in values.items()}
derived=json.loads((ROOT/'independent_derived_formulas.json').read_text())
def rational(expr,label):
    nn,dd=S.fraction(S.cancel(expr));return divide(evaluate_poly(nn,values,M),evaluate_poly(dd,values,M),M,label)[0]
values[g]=rational(u/(q*t),'g');values[s]=rational(t/q,'s');values[o]=values[i]-values[a]
values[p]=-(values[i]*values[q]).truncate(M);values[c]=rational(parse(derived['c']),'c')
v2=rational(parse(derived['v2']),'v2');output=rational(parse(derived['G']),'G')
assert output.truncate(M)==G.truncate(M),'G output agrees exactly to known precision'
center=read('seven_parameter_full_system_certificate.json')['center_jet_degree8']
jets={}
for v in (g,i,p,q,s,c,o):
    jets[str(v)]=[str(values[v][k]) for k in range(5)]
    assert jets[str(v)]==center[str(v)][:5],(str(v),jets[str(v)],center[str(v)][:5])
print('All seven reconstructed coordinates lie in accepted Hensel ball',flush=True)
# Each source denominator is explicitly nonzero, including the original system.
unit_constants={}
for name,rows in [('changed',list(read('changed_scalar_coordinates.json')['equations'].values())),('six',read('six_parameter_selected_system.json')['equations']),('original',read('seven_scalar_numerators.json')['equations'])]:
    for k,row in enumerate(rows):
        const=evaluate_poly(parse(row['denominator']),values,M)[0];assert const,(name,k)
        unit_constants[f'{name}_{k}']=str(const)
coef=parse(read('five_scalar_reduction.json')['c_elimination']['coefficient'])
unit_constants['c_elimination_coefficient']=str(rational(coef,'c_elimination_coefficient')[0]);assert fmpq(unit_constants['c_elimination_coefficient'])
assert v2[0]==3
# Exact finite jets justify regularity/nonvanishing, never infinite identities.
receipt={'status':'PASS','P_terms':len(P.to_dict()),'P_degrees':list(map(int,P.degrees())),'substitution_x_valuation':valuation,'simple_quotient_constant':'-16*(z-325692)*(z-325656)','simple_derivative':'-576','branch_condition':'G = 1+x+2x^2+6x^3+24x^4+120x^5+720x^6+5004x^7+38844x^8+325692x^9 mod x^10','G_precision_modulus':N,'G_coefficients':[str(G[k]) for k in range(N)],'map_ledger':ledger,'common_reconstructed_precision':M,'selected_seven_jets':jets,'source_denominator_constants':unit_constants,'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'desingularized_polynomial.json').write_text(json.dumps({'variables':['z','x'],'terms':[[int(j),int(k),str(co)] for (j,k),co in sorted(H.to_dict().items())]},indent=2)+'\n')
(ROOT/'branch_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2),flush=True)
