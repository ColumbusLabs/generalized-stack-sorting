"""Exact, fixed-size symbolic certificate for the derived (2,3) quintic.
Requires SymPy.
No coefficient fit or new permutation census. All resultants have fixed degree.
"""
from pathlib import Path
import argparse,hashlib,json,time
import sympy as sp
x,z,g,b,c,F,H=sp.symbols('x z g b c F H')
E=sp.eye(4);e=[E.row(i) for i in range(4)]
start=time.perf_counter()
u=sp.Matrix([[x*g,g,b,c]])
v=(1+x)*u+e[2]-e[1]-x*e[0]
d=1-x*c
wn=2*x*g*u+x*b*v+g*e[3]
M=sp.Matrix.vstack(e[0]-z*u,e[1]-z*e[3]-2*x*z*u,e[2]-2*x*z*v,d*e[3]-2*x*z*wn)
B0=sp.eye(4);B0[1,3]=z;B0[3,3]=d
Delta=sp.factor(M.det(method='domain-ge'))
r=v*M.adjugate(method='berkowitz');r=[sp.factor(y) for y in r]
h=[sp.factor(sum(r[i]*B0[i,j] for i in range(4))) for j in range(4)]
K=sp.factor(((z-1)*(1-2*x*z)-x*z)*Delta-x*z**3*(z-1)*r[0])
N=[]
for j,t in zip((1,2,3),(g-1,b,c)):
    seed=z if j==1 else z*z if j==2 else 0
    N.append(sp.factor((z-1)*Delta*seed-z*Delta*t+x*z**3*(z-1)*h[j]))
assert sp.expand(K.subs({x:0,g:1,b:0,c:0}))==z-1
# A kernel root Z=1+x+O(x^2) exists, regardless of higher initial coefficients.
g1,b1,c1=sp.symbols('g1 b1 c1')
assert sp.series(K.subs({z:1+x,g:1+g1*x,b:b1*x,c:c1*x},simultaneous=True),x,0,2).removeO()==0
Lbc,rhs=sp.linear_eq_to_matrix([sp.expand(K),sp.expand(N[0]/z)],[b,c])
detbc=sp.factor(Lbc.det());adjb=sp.factor((Lbc.adjugate()*rhs)[0])
J=4*g*x*z-g*x-g+1
G=g*x*z+x*z*z-x*z-z+1
Q=2*g*x*x*z*z-g*x*x*z-g*x*z-4*x*z+x+1
assert sp.expand(detbc-2*x**3*z**3*(z-1)*J*G*Q)==0
assert sp.expand(detbc*b-adjb-2*x**3*z**3*(z-1)*G*Q*(b*J-2*g*g*(1-2*x*z)))==0
# All other factors are nonzero on the formal branch, so G=0.
gz=(z-1)*(1-x*z)/(x*z)
P=[sp.cancel(y.subs(g,gz)) for y in [K]+N]
assert sp.cancel(P[1]+P[0]/x)==0
Q0=sp.Poly(P[0],c)
assert Q0.degree()==1
Ac=sp.factor(Q0.coeff_monomial(c));Bc=sp.factor(Q0.coeff_monomial(1))
D=sp.cancel(Ac/(x*z));assert sp.denom(D)==1
C=-Bc/Ac
n2=sp.Poly(P[2],c);n3=sp.Poly(P[3],c)
assert n2.degree()==1 and n3.degree()==2
E2=sp.factor(Ac*n2.coeff_monomial(1)-Bc*n2.coeff_monomial(c))
E3=sp.factor(Bc**2*n3.coeff_monomial(c**2)-Ac*Bc*n3.coeff_monomial(c)+Ac**2*n3.coeff_monomial(1))
assert sp.expand(Ac*P[2]-E2-n2.coeff_monomial(c)*P[0])==0
assert sp.expand(Ac**2*P[3]-E3-P[0]*(n3.coeff_monomial(c**2)*(Ac*c-Bc)+n3.coeff_monomial(c)*Ac))==0
L=2*x*x*z**3-3*x*x*z*z+x*x*z-3*x*z*z+8*x*z-2*x+z-2
Q2=sp.cancel(E2/(-2*x*x*z**4*(z-1)*L))
Q3=sp.cancel(E3/(2*x*x*z**5*(z-1)*L))
assert sp.denom(Q2)==sp.denom(Q3)==1
assert sp.degree(Q2,b)==sp.degree(Q3,b)==2
resb=sp.factor(sp.resultant(Q2,Q3,b))
R10=sp.cancel(resb/(-4*x**6*z**6*(z-1)*(x*z-1)*D**2))
assert sp.denom(R10)==1 and sp.degree(R10,z)==10
# Exact short initial terms exclude the denominator factor D.
gshort=1+x+3*x*x+13*x**3
Zshort=sp.Integer(1)
for _ in range(5):Zshort=sp.series(1+x*Zshort*(Zshort-1+gshort),x,0,5).removeO()
Dshort=sp.series(D.subs(z,Zshort),x,0,5).removeO()
assert Dshort==-4*x**4
# Final polynomial, with positive leading F coefficient.
P5=((1+3*x)*F**5-(6+29*x-23*x*x+6*x**3)*F**4
    +(15+94*x-99*x*x+31*x**3-2*x**4)*F**3
    -(19+143*x-157*x*x+49*x**3-5*x**4)*F**2
    +(12+105*x-102*x*x+21*x**3)*F-(3+30*x-21*x*x))
resF=sp.resultant(R10,F*(1+x*z*z-x*z)-z,z)
assert sp.expand(resF-x**5*P5**2)==0
# Correct branch is uniquely determined by its coefficients through degree four.
branch=sp.Poly(sp.expand(P5.subs(F,1+x+2*x*x+6*x**3+24*x**4+x**5*H)),x)
valuation=min(power[0] for power,coef in branch.terms())
assert valuation==10
initial=sp.expand(branch.as_expr()/x**10).subs(x,0)
assert sp.expand(initial+6*(H-120))==0
# Finite-field irreducibility witness at x=4 modulo 5, normalized to monic.
q=sp.Poly(P5.subs(x,4),F,modulus=5).monic()
expected_q=sp.Poly(F**5-F**4-2*F**3-2*F+1,F,modulus=5)
assert q==expected_q
y=sp.Poly(F,F,modulus=5);powers=[]
for _ in range(5):
    y=sp.rem(y**5,q);powers.append(str(y.as_expr()))
assert y==sp.Poly(F,F,modulus=5)
a=sp.rem(sp.Poly(F**5-F,F,modulus=5),q)
bez1,bez2,gcd=sp.gcdex(q,a)
assert gcd==sp.Poly(1,F,modulus=5)
assert bez1*q+bez2*a==sp.Poly(1,F,modulus=5)
assert sp.gcd(sp.Poly(1+3*x,x),sp.Poly(3+30*x-21*x*x,x)).degree()==0
# Optional finite consistency check against already existing exact data.
ap=argparse.ArgumentParser();ap.add_argument('--reference-counts',type=Path);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
report={'status':'passed','scope':'exact fixed-size symbolic derivation and irreducibility/branch certificates; conditional on the stated first-return and kernel identities','polynomial':str(sp.expand(P5)),'kernel_polynomial':str(sp.expand(K)),'kernel_numerators':[str(sp.expand(y)) for y in N],'det_bc':str(detbc),'singular_branch_identity_factor':str(G),'D':str(D),'Q2':str(Q2),'Q3':str(Q3),'kernel_root_polynomial':str(R10),'kernel_root_degree':10,'polynomial_degrees':{'x':4,'F':5},'polynomial_terms':len(sp.Poly(P5,x,F).terms()),'branch_initial_polynomial':str(initial),'D_initial':str(Dshort),'irreducibility':{'specialize_x':4,'prime':5,'monic_polynomial':str(q.as_expr()),'frobenius_remainders':powers,'bezout_q':str(bez1.as_expr()),'bezout_fifth_minus_F':str(bez2.as_expr())},'sympy_version':sp.__version__,'seconds':time.perf_counter()-start,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
if args.reference_counts:
    raw=args.reference_counts.read_bytes();seq=json.loads(raw)['counts'];NN=min(26,len(seq)-1)
    seq=seq[:NN+1];mul=lambda a,b:[sum(a[i]*b[n-i] for i in range(n+1)) for n in range(NN+1)]
    fp=[[1]+[0]*NN]
    for _ in range(5):fp.append(mul(fp[-1],seq))
    residues=[0]*(NN+1)
    for (dx,df),coef in sp.Poly(P5,x,F).terms():
        for n in range(dx,NN+1):residues[n]+=int(coef)*fp[df][n-dx]
    assert not any(residues)
    report['finite_check']={'max_n':NN,'all_residues_zero':True,'reference_sha256':hashlib.sha256(raw).hexdigest()}
args.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('status','polynomial_degrees','polynomial_terms','seconds','sympy_version')},indent=2))
