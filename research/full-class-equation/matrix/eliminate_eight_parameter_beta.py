#!/usr/bin/env python3
"""Exact triangular elimination of beta in the eight-parameter graph family."""
from pathlib import Path
import sympy as s,json,time,resource
resource.setrlimit(resource.RLIMIT_AS,(768<<20,768<<20));P=Path(__file__).resolve().parent;start=time.monotonic();d=json.loads((P/'eight_parameter_epsilon_constraints.json').read_text());vars=s.symbols('g i p q s c o w');g,ii,p,q,ss,c,o,w=vars;bs=s.symbols('beta0:6');loc={str(z):z for z in vars+bs};eqs={name:s.sympify(e['numerator'],locals=loc)/s.sympify(e['denominator'],locals=loc) for name,e in d['equations'].items() if name.startswith(('ZE','BE','TE','initial'))}
constant=dict(zip(vars,[12,8,s.Rational(-4,9),s.Rational(1,18),s.Rational(9,2),2,6,9]));sub={};steps=[]
for name,b in [('BE_2',bs[2]),('BE_3',bs[3]),('BE_5',bs[5])]:
 ex=s.cancel(eqs[name].subs(sub));coef=s.cancel(s.diff(ex,b));answer=s.cancel(-(ex-coef*b)/coef);sub[b]=answer;steps.append({'equation':name,'solved':str(b),'coefficient':str(coef),'coefficient_at_constant':str(coef.subs(constant)),'answer':str(answer)});print(name,'solved',b,'chars',len(str(answer)),time.monotonic()-start,flush=True)
for name in ['ZE_4','initial_ZZ_0']:
 ex=s.cancel(eqs[name].subs(sub));print('prospective',name,'chars',len(str(ex)),'coefs',[str(s.diff(ex,z).subs(constant)) for z in [bs[0],bs[1],bs[4]]],flush=True)
# Fourth B/Z pivot is selected only after checking its unit coefficient.
ex=s.cancel(eqs['ZE_4'].subs(sub));coef=s.cancel(s.diff(ex,bs[4]));assert coef.subs(constant)!=0
answer=s.cancel(-(ex-coef*bs[4])/coef);sub[bs[4]]=answer;steps.append({'equation':'ZE_4','solved':'beta4','coefficient':str(coef),'coefficient_at_constant':str(coef.subs(constant)),'answer':str(answer)})
# Compose the triangular substitutions before the T equation.
sub={z:s.cancel(v.subs({bs[4]:answer})) for z,v in sub.items()}
ex=s.cancel(eqs['TE_1'].subs(sub));coef=s.cancel(s.diff(ex,bs[1]));assert coef.subs(constant)!=0
answer=s.cancel(-(ex-coef*bs[1])/coef);sub[bs[1]]=answer;steps.append({'equation':'TE_1','solved':'beta1','coefficient':str(coef),'coefficient_at_constant':str(coef.subs(constant)),'answer':str(answer)})
sub={z:s.cancel(v.subs({bs[1]:answer})) for z,v in sub.items()}
reduced={}
for name,ex in eqs.items():
 val=s.cancel(ex.subs(sub));num,den=val.as_numer_denom()
 if num:reduced[name]={'numerator':str(s.factor(num)),'denominator':str(s.factor(den))}
 print(name,'zero' if num==0 else 'nonzero','seconds',time.monotonic()-start,flush=True)
result={'scope':'Exact rational beta elimination for the conditional eight-parameter full graph equations. Remaining scalar constraints still need a formal branch.','variables':list(map(str,vars)),'steps':steps,'beta_over_beta0':{str(z):str(s.cancel(v/bs[0])) for z,v in sub.items()},'remaining_E_constraints':reduced,'seconds':time.monotonic()-start}
(P/'eight_parameter_beta_elimination.json').write_text(json.dumps(result,indent=2)+'\n');print('remaining',reduced,'seconds',time.monotonic()-start,flush=True)
