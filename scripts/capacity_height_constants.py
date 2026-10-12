"""Bounded exact algebraic-number check of the capacity-height normalization.

This is supplementary algebra evidence, not a probability proof or Lean result.
No permutation enumeration is performed.
"""
import json
import sympy as s
from sympy import QQ

x,a,b,t=s.symbols('x a b t')
p=6*t**3+2*t**2-5*t+1
root=s.CRootOf(p,1)  # the middle real root, uniquely in (0,1/3)
F=QQ.algebraic_field(root)
q=F.from_sympy(root)
one=F.one
rho=q*(one-3*q)/((one+q)*(one-2*q-2*q*q))
L=one+q
K=(one-2*q-2*q*q)/(one-3*q)
tau=[q,q*q/(one-3*q)]
G=[x*(1+a+b)/(1-x*(1+a+b)),
   x*(a+3*b)/((1-x*(1+2*a+4*b))*(1-x*(1+a+b)))]

def evaluate(expr):
    num,den=s.fraction(s.factor(expr))
    def poly_value(poly):
        out=F.zero
        for powers,c in s.Poly(poly,x,a,b).terms():
            v=F.from_sympy(c)
            for base,power in zip([rho,*tau],powers):
                v*=base**power
            out+=v
        return out
    return poly_value(num)/poly_value(den)

J=[[evaluate(s.diff(g,y)) for y in (a,b)] for g in G]
M=[[J[i][j]*tau[j]/tau[i] for j in range(2)] for i in range(2)]
left=[M[1][0],one-M[0][0]]
den=sum(left,F.zero)
left=[v/den for v in left]
right=[M[0][1],one-M[0][0]]
den=sum((left[i]*right[i] for i in range(2)),F.zero)
right=[v/den for v in right]
mu=sum((left[i]*rho*evaluate(s.diff(G[i],x))/tau[i] for i in range(2)),F.zero)
sigma2=F.zero
for i in range(2):
    for j,y in enumerate((a,b)):
        for k,z in enumerate((a,b)):
            sigma2+=left[i]*right[j]*right[k]*tau[j]*tau[k]*evaluate(s.diff(G[i],y,z))/tau[i]
A=(K*(K-one)/rho-2*rho*K**3*L**2)/(one-2*q*q)
B=(one-2*q**3)/(K*(one-2*q*q))
checks={
 'fixed_point_A':evaluate(G[0])==tau[0],
 'fixed_point_B':evaluate(G[1])==tau[1],
 'eigenvalue_one':(one-J[0][0])*(one-J[1][1])-J[0][1]*J[1][0]==F.zero,
 'other_eigenvalue_2t2':J[0][0]+J[1][1]==one+2*q*q,
 'variance_mass_equals_2rhoAB':sigma2*mu==2*rho*A*B,
}
assert all(checks.values()),checks
values={name:str(s.N(F.to_sympy(value),35)) for name,value in {
 't':q,'rho':rho,'mu':mu,'sigma_squared':sigma2,'pole_AB':A*B}.items()}
values['capacity_excursion_factor']=str(s.N(2/s.sqrt(F.to_sympy(mu*sigma2)),35))
print(json.dumps({'exact_checks_in_cubic_number_field':checks,
 'numerical_diagnostics':values,'sympy_version':s.__version__},indent=2))
