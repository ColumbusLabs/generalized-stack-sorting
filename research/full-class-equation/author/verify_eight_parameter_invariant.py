#!/usr/bin/env python3
"""Exact replay of the rational non-E invariant chart, independent of its solving steps."""
import json,sympy as sp,resource,time,hashlib
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512<<20,512<<20));start=time.monotonic();root=Path(__file__).parent
src=root/'eight-parameter-matrix-closure.json';data=json.loads(src.read_text());vs=sp.symbols('g i p q s c o w');g,i,p,q,s,c,o,w=vs;local=dict(zip(data['free_variables'],vs))
A=sp.Matrix([[sp.sympify(v,locals=local) for v in row] for row in data['A']]);T=sp.Matrix([[sp.sympify(v,locals=local) for v in row] for row in data['T']]);e=lambda k:sp.eye(6)[k,:];I=[0,1,4];E=sp.Matrix.vstack(e(0),e(1),e(4));a=e(0)+p*(e(1)-e(3))+q*(e(4)-e(5));R=sp.Matrix.vstack(a,e(3),e(5));B=A*E;Z=A*R;L=B-Z;C=B.extract(I,I);Ci=C.inv();V=(A*Ci).applyfunc(sp.cancel);W=L[:,[1,4]].applyfunc(sp.cancel);P=(Z[I,:]*V).applyfunc(sp.cancel);Q=(Z[I,:]*W).applyfunc(sp.cancel);D=sp.Matrix.vstack(e(1)-e(3),e(4)-e(5))*W
f0=sp.Matrix([[1,0,0]]);f1=sp.Matrix([[0,1,0]]);u=-2*f0*Ci;HF=sp.Matrix.vstack(u,u*P-f0,-3*f0,-f0,(u*P-f0)*P-f1,-f1).applyfunc(sp.cancel)
HJ=sp.zeros(6,3);HJ[3,:]=-2*a*V;HJ[5,:]=-e(3)*V-2*a*Z*V;HJ=HJ.applyfunc(sp.cancel)
HK=sp.zeros(6,2);HK[0,:]=sp.Matrix([[2*p,2*q]]);HK[1,:]=-(e(0)+2*a)*W;HK[2,:]=-3*e(0)*W;HK[4,:]=HF[1,:]*Q-W[1,:];HK=HK.applyfunc(sp.cancel)
checks={'C2':Z*T-B*Z-Z*B+Z*Z,'BF':B*HF-HF*P+V,'ZF':Z*HF+V,'TF':T*HF-HF*C+V,'BJ':B*HJ,'ZJ':Z*HJ-HF*P,'TJ':T*HJ-HJ*P,'BK':B*HK-HF*Q+W,'ZK':Z*HK,'TK':T*HK-HF*Q-HK*D+W,'Z_boundary_F':a*HF+f0*Ci,'Z_boundary_J':a*HJ*P+a*V,'Z_boundary_K':a*HK,'low_FQ':HF*Q+W,'alpha_shape_V':sp.Matrix([[1,0,0]])+p*(V[1,:]-V[3,:])+q*(V[4,:]-V[5,:])-a*V}
counts={}
for name,M in checks.items():
 for pos,v in enumerate(M):assert sp.cancel(v)==0,(name,pos,sp.factor(v))
 counts[name]=len(M);print(name,'PASS',len(M),flush=True)
constants={g:12,i:8,p:sp.Rational(-4,9),q:sp.Rational(1,18),s:sp.Rational(9,2),c:2,o:6,w:9};units={'q':q,'s':s,'g':g,'det_C':C.det(),'det_D':D.det(),'det_HF_I':HF[I,:].det()};units={name:str(sp.cancel(v).subs(constants)) for name,v in units.items()};assert all(sp.Rational(v)!=0 for v in units.values())
out={'scope':'Exact rational identity verification for the eight-parameter ansatz, independent of branch values. This certifies non-E invariant closure only; E-column, terminal/boundary scalar constraints and formal-branch existence remain separate.','status':'PASS','exact_scalar_zero_identities':counts,'count':sum(counts.values()),'unit_values_at_initial_tuple':units,'parameter_constants':{str(k):str(v) for k,v in constants.items()},'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(root/'eight-parameter-invariant-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
