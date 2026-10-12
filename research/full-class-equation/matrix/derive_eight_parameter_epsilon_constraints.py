#!/usr/bin/env python3
"""Exact symbolic E-column and terminal constraints, conditional on the matrix ansatz."""
from pathlib import Path
import sympy as s,json,time,hashlib,resource
resource.setrlimit(resource.RLIMIT_AS,(640<<20,640<<20))
Pdir=Path(__file__).resolve().parent;start=time.monotonic()
resource_file=Path(__file__).with_name('eight-parameter-matrix-closure.json')
family=json.loads(resource_file.read_text());v=s.symbols(' '.join(family['free_variables']));g,ii,p,q,ss,c,o,w=v;locals0={str(a):a for a in v};A=s.Matrix([[s.sympify(e,locals=locals0) for e in row] for row in family['A']]);T=s.Matrix([[s.sympify(e,locals=locals0) for e in row] for row in family['T']]);h=s.sympify(family['h'],locals=locals0)
I=[0,1,4];E6=s.eye(6);e=lambda k:E6[k,:];E=s.Matrix.vstack(e(0),e(1),e(4));dif=s.Matrix.vstack(e(1)-e(3),e(4)-e(5));alpha=e(0)+p*dif[0,:]+q*dif[1,:];R=s.Matrix.vstack(alpha,e(3),e(5));B=A*E;Z=A*R;L=B-Z;C=B.extract(I,I);Ci=C.inv();V=(A*Ci).applyfunc(s.cancel);W=L[:,[1,4]].applyfunc(s.cancel);P=(Z[I,:]*V).applyfunc(s.cancel);Q=(Z[I,:]*W).applyfunc(s.cancel);D=dif*W
x0=s.Matrix([[1,0,0]]);x1=s.Matrix([[0,1,0]]);hf0=-2*x0*Ci
HF=s.Matrix.vstack(hf0,hf0*P-x0,-3*x0,-x0,(hf0*P-x0)*P-x1,-x1).applyfunc(s.cancel)
HJ=s.zeros(6,3);HJ[3,:]=-2*alpha*V;HJ[5,:]=-e(3)*V-2*alpha*Z*V;HJ=HJ.applyfunc(s.cancel)
HK=s.zeros(6,2);HK[0,:]=s.Matrix([[2*p,2*q]]);HK[1,:]=-(e(0)+2*alpha)*W;HK[2,:]=-3*e(0)*W;HK[4,:]=HF[1,:]*Q-W[1,:];HK=HK.applyfunc(s.cancel)
# E above selects I; no beta variables enter these matrix definitions.
Mu=s.eye(6)-V*E;RZ=Z[I,:]-P*E;RB=B[I,:];RT=RB-P*E
UU=s.zeros(6,6);UU[1,:]=-2*e(0)+2*alpha*V*E;UU[2,:]=s.zeros(1,6);UU[3,:]=-2*alpha*Mu
UU[4,:]=HF[1,:]*RZ+HK[1,:]*dif;UU[5,:]=HF[1,:]*RZ
UU[0,:]=(HF[4,:]*RZ+HK[4,:]*dif-h*UU[1,:]-ii*UU[4,:])/g
UU=UU.applyfunc(s.cancel)
KE=((HF+HJ)*E+UU).applyfunc(s.cancel)
# Exact E-columns of graph closure and projected Z-family containment.
EP={'ZE':Z*UU-HF*RZ-HJ*Z[I,:]+Mu,'BE':B*UU-HF*RZ-HJ*RB-HK*dif+Mu,'TE':T*UU-HJ*RT+Mu,'initial_ZZ':alpha*Z*UU+2*alpha*Mu+alpha,'initial_ZB':alpha*B*UU+2*alpha*Mu+e(0),'initial_ZT':alpha*T*UU+2*alpha*Mu+e(0)-alpha}
bs=s.symbols('beta0:6');beta=s.Matrix(bs);linear_eqs={};stats={}
for name,MAT in EP.items():
 MM=MAT.applyfunc(s.cancel);nonzero=sum(z!=0 for z in MM);stats[name]={'nonzero_matrix_entries':nonzero}
 vector=MM*beta
 for i,z in enumerate(vector):
  num,den=s.cancel(z).as_numer_denom()
  if num!=0:linear_eqs[f'{name}_{i}']={'numerator':str(s.factor(num)),'denominator':str(s.factor(den))}
 print(name,'entries',nonzero,'equations',sum(k.startswith(name+'_') for k in linear_eqs),'seconds',time.monotonic()-start,flush=True)
xx=s.symbols('x');rs=s.symbols('r0:6');rv=s.Matrix(rs);dd=s.symbols('d0')
for i,z in enumerate(beta-xx*rv+KE*beta):
 num,den=s.cancel(z).as_numer_denom();linear_eqs[f'terminal_{i}']={'numerator':str(s.factor(num)),'denominator':str(s.factor(den))}
for i,z in enumerate(rv-beta-xx*T*rv):
 num,den=s.cancel(z).as_numer_denom();linear_eqs[f'resolvent_{i}']={'numerator':str(s.factor(num)),'denominator':str(s.factor(den))}
for name,z in [('empty_B',(e(0)*(beta-xx*rv))[0]-2*dd),('empty_Z',(alpha*(beta-xx*rv))[0]-2*dd),('height_one',(1-2*xx)*dd-1-xx**2*rv[0])]:
 num,den=s.cancel(z).as_numer_denom();linear_eqs[name]={'numerator':str(s.factor(num)),'denominator':str(s.factor(den))}
out={'scope':'Exact conditional rational graph identities; no claim they hold on the selected branch. E-column constraints are linear in beta; terminal/boundary equations are linear in beta,r,d0 for fixed matrix parameters and x.','matrix_variables':list(map(str,v)),'linear_unknowns':list(map(str,bs+rs+(dd,))),'parameter':'x','stats':stats,'U_rows':[[str(z) for z in UU[i,:]] for i in range(6)],'K_rows':[[str(z) for z in KE[i,:]] for i in range(6)],'equations':linear_eqs,'seconds':time.monotonic()-start,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(Pdir/'eight_parameter_epsilon_constraints.json').write_text(json.dumps(out,indent=2)+'\n');print('total',len(linear_eqs),'seconds',time.monotonic()-start,flush=True)
