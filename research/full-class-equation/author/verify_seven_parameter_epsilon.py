#!/usr/bin/env python3
"""Independent exact replay of beta elimination and all E-column graph identities."""
from pathlib import Path
import json,sympy as sp,resource,time,hashlib
resource.setrlimit(resource.RLIMIT_AS,(512<<20,512<<20));start=time.monotonic();root=Path(__file__).parent;other=Path(__file__).resolve().parent.parent/'matrix'
family_path=root/'eight-parameter-matrix-closure.json';beta_path=other/'eight_parameter_beta_elimination.json';constraints_path=other/'eight_parameter_epsilon_constraints.json'
family=json.loads(family_path.read_text());beta_data=json.loads(beta_path.read_text());constraints=json.loads(constraints_path.read_text());vs=sp.symbols('g i p q s c o w');g,i,p,q,s,c,o,w=vs;local=dict(zip(family['free_variables'],vs));const={g:12,i:8,p:sp.Rational(-4,9),q:sp.Rational(1,18),s:sp.Rational(9,2),c:2,o:6,w:9}
ratio=sp.Matrix([1]+[sp.sympify(beta_data['beta_over_beta0']['beta'+str(k)],locals=local) for k in range(1,6)]);beta_symbols=sp.symbols('beta0:6');sub=dict(zip(beta_symbols,ratio));cancel=sp.cancel
checks={};before={}
for name,row in constraints['equations'].items():
 if not name.startswith(('ZE_','BE_','TE_','initial_')):continue
 expr=sp.sympify(row['numerator'],locals=local)/sp.sympify(row['denominator'],locals=local)
 rem=cancel(expr.subs(sub, simultaneous=True));before[name]=str(sp.factor(rem))
 after=cancel(rem.subs(w,3*o/2));assert after==0,(name,after);checks[name]=True
assert [name for name,value in before.items() if value!='0']==['TE_2']
expected=-3*g*q**2*(-3*o+2*w)/(2*(-6*g*o*q**3*s-6*g*p*q**2*s-2*g*q**2+6*i*o*q**2*s+6*i*p*q*s+3*i*q+6*o*p*q*s+6*p**2*s+3*p))
assert cancel(sp.sympify(before['TE_2'],locals=local)-expected)==0
ratio=ratio.subs(w,3*o/2).applyfunc(cancel)
ratio_constants=[str(cancel(v).subs(const)) for v in ratio];assert ratio_constants==['1','3','3','3','12','12']
ratio_den_constants=[str(cancel(v).as_numer_denom()[1].subs(const)) for v in ratio];assert all(sp.Rational(v)!=0 for v in ratio_den_constants)
print('Parsed 14 E constraints and unique w constraint PASS',flush=True)
# Rebuild all nine-dimensional suffix blocks and E-column graph from the matrix family;
# do not use exported E constraints in this second part.
A=sp.Matrix([[sp.sympify(v,locals=local) for v in row] for row in family['A']]);T=sp.Matrix([[sp.sympify(v,locals=local) for v in row] for row in family['T']]).subs(w,3*o/2)
e=lambda k:sp.eye(6)[k,:];I=[0,1,4];E=sp.Matrix.vstack(e(0),e(1),e(4));diff=sp.Matrix.vstack(e(1)-e(3),e(4)-e(5));alpha=e(0)+p*diff[0,:]+q*diff[1,:];R=sp.Matrix.vstack(alpha,e(3),e(5));B=A*E;Z=A*R;L=B-Z;C=B.extract(I,I);Ci=C.inv();V=(A*Ci).applyfunc(cancel);W=L[:,[1,4]].applyfunc(cancel);P=(Z[I,:]*V).applyfunc(cancel);Q=(Z[I,:]*W).applyfunc(cancel)
f0=sp.Matrix([[1,0,0]]);f1=sp.Matrix([[0,1,0]]);u=-2*f0*Ci
HF=sp.Matrix.vstack(u,u*P-f0,-3*f0,-f0,(u*P-f0)*P-f1,-f1).applyfunc(cancel)
HJ=sp.zeros(6,3);HJ[3,:]=-2*alpha*V;HJ[5,:]=-e(3)*V-2*alpha*Z*V;HJ=HJ.applyfunc(cancel)
HK=sp.zeros(6,2);HK[0,:]=sp.Matrix([[2*p,2*q]]);HK[1,:]=-(e(0)+2*alpha)*W;HK[2,:]=-3*e(0)*W;HK[4,:]=HF[1,:]*Q-W[1,:];HK=HK.applyfunc(cancel)
Mu=sp.eye(6)-V*E;RZ=Z[I,:]-P*E;RB=B[I,:];RT=RB-P*E
U=sp.zeros(6,6);U[1,:]=-2*e(0)+2*alpha*V*E;U[3,:]=-2*alpha*Mu;U[4,:]=HF[1,:]*RZ+HK[1,:]*diff;U[5,:]=HF[1,:]*RZ;U[0,:]=(HF[4,:]*RZ+HK[4,:]*diff-B[4,1]*U[1,:]-B[4,4]*U[4,:])/B[4,0];U=U.applyfunc(cancel);HE=(U*ratio).applyfunc(cancel)
rebuild_matrices={
 'B_E':B*U-HF*RZ-HJ*RB-HK*diff+Mu,
 'Z_E':Z*U-HF*RZ-HJ*Z[I,:]+Mu,
 'T_E':T*U-HJ*RT+Mu,
 'initial_ZZ':alpha*Z*U+2*alpha*Mu+alpha,
 'initial_ZB':alpha*B*U+2*alpha*Mu+e(0),
 'initial_ZT':alpha*T*U+2*alpha*Mu+e(0)-alpha}
rebuild={name:mat.applyfunc(cancel)*ratio for name,mat in rebuild_matrices.items()}
rebuild_counts={}
for name,mat in rebuild.items():
 for index,expr in enumerate(mat):assert cancel(expr)==0,(name,index,sp.factor(expr))
 rebuild_counts[name]=len(mat);print(name,'PASS',len(mat),flush=True)
K=((HF+HJ)*E+U).applyfunc(cancel)
# Independently compare K against the compact row formulas used in the seven-system.
Kcompact=sp.zeros(6,6);Kcompact[1,:]=Kcompact[2,:]=-3*e(0);Kcompact[3,:]=-e(0)-2*alpha;Kcompact[4,:]=-2*e(1)-2*alpha*B;Kcompact[5,:]=-e(1)-e(3)-2*alpha*Z;Kcompact[0,:]=(3*B[4,1]*e(0)+2*B[4,4]*e(1)-2*e(4)-e(3)*B-2*alpha*Z*B+2*B[4,4]*alpha*B)/g
for expr in K-Kcompact:assert cancel(expr)==0
out={'status':'PASS','scope':'Exact rational identities over Q(g,i,p,q,s,c,o), with w=3o/2. Certifies all E-column graph and initial-row identities plus the compact K formula; does not assert formal branch existence.','parsed_E_constraints':len(checks),'only_pre_substitution_residual':before['TE_2'],'rebuilt_graph_scalar_identity_counts':rebuild_counts,'compact_K_scalar_identities':36,'beta_direction_constants':ratio_constants,'beta_ratio_denominator_constants':ratio_den_constants,'parameter_constants':{str(k):str(v) for k,v in const.items()},'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [family_path,beta_path,constraints_path]},'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(root/'seven-parameter-epsilon-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
