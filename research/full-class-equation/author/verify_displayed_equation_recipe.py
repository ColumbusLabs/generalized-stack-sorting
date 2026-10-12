#!/usr/bin/env python3
"""Replay the compact displayed matrix recipe against the frozen explicit entries."""
from pathlib import Path
import json,sympy as S,time,resource,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512<<20,512<<20));start=time.monotonic();root=Path(__file__).parent
vs=S.symbols('g i p q s c o');g,i,p,q,s,c,o=vs;h=(2*i*p*q*s+i*q+2*p*p*s+p-2*q*s)/(2*q*q*s);z0=1+q*(h-p*g);z1=p+q*(i-q*g)
d=-1/(2*q)-s*(p/q+q*g);j=g-(s+p*d)/q;e=p*d-s*z0;f=q*d+S.Rational(1,2)-s*z1;k=h-p*g+p*j-p*(e-p*d)/q+1/(2*q);ell=i-q*g+q*j-p*(f-q*d)/q+p/q;a=(c-S.Rational(3,2)+3*s*z1)/q;b=p*a-3*s*z0
A=S.Matrix([[0,1,0],[0,0,1],[a,b,c],[d,e,f],[g,h,i],[j,k,ell]]).applyfunc(S.cancel)
ey=S.eye(6);er=lambda j:ey[j,:];I=[0,1,4];E=S.Matrix.vstack(er(0),er(1),er(4));alpha=er(0)+p*(er(1)-er(3))+q*(er(4)-er(5));B=A*E;Z=A*S.Matrix.vstack(alpha,er(3),er(5));L=B-Z;C=B[I,I];V=(A*C.inv()).applyfunc(S.cancel);W=L[:,[1,4]];P=(Z[I,:]*V).applyfunc(S.cancel);Q=Z[I,:]*W;f0=S.Matrix([[1,0,0]]);f1=S.Matrix([[0,1,0]]);u=-2*f0*C.inv();HF=S.Matrix.vstack(u,u*P-f0,-3*f0,-f0,(u*P-f0)*P-f1,-f1).applyfunc(S.cancel)
T=S.zeros(6,6);T[0,:]=er(2);T[3,:]=er(5)+L[3,:];T[5,:]=Z[4,:]+L[5,:]
for row,free in [(1,o),(2,3*o/2)]:
 coeff=((HF[row,:]*C-V[row,:]-free*HF[2,:])*HF[I,:].inv()).applyfunc(S.cancel)
 for jj,col in enumerate(I):T[row,col]=coeff[jj]
 T[row,2]=free
T[4,:]=(er(3)-er(2)+alpha*L+p*T[3,:]+q*T[5,:]-p*T[1,:])/q
src=root/'eight-parameter-matrix-closure.json';family=json.loads(src.read_text());locals0={str(v):v for v in vs};locals0['w']=3*o/2
checks={}
for name,value in [('A',A),('T',T)]:
 expected=S.Matrix([[S.sympify(z,locals=locals0) for z in row] for row in family[name]])
 for z in value-expected:assert S.cancel(z)==0
 checks[name]=len(value)
out={'status':'PASS','scope':'The displayed seven-parameter matrix recipe agrees entrywise with the frozen explicit matrix family after w=3o/2.','scalar_identities':checks,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'theorem_sha256':hashlib.sha256((root/'explicit-seven-equation-theorem.md').read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(root/'displayed-equation-recipe-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
