#!/usr/bin/env python3
"""Explicit polynomial lift of the full seven-parameter graph equations."""
from pathlib import Path
import sympy as sp,json,hashlib,time,resource
resource.setrlimit(resource.RLIMIT_AS,(768<<20,768<<20));P=Path(__file__).resolve().parent;start=time.monotonic()
fam=json.loads(Path(__file__).with_name('eight-parameter-matrix-closure.json').read_text());rat=json.loads((P/'eight_parameter_beta_elimination.json').read_text());cert=json.loads((P/'seven_parameter_full_system_certificate.json').read_text());names=cert['variables'];syms=sp.symbols(' '.join(names));loc=dict(zip(names,syms));loc['w']=3*loc['o']/2
nodes=[];memo={};units={}
def node(t):
 if t not in memo:memo[t]=len(nodes);nodes.append(list(t))
 return memo[t]
def constant(v):
 v=sp.Rational(v);return node(('rational',str(v)))
z=constant(0);one=constant(1);negone=constant(-1);x=node(('parameter','x'))
def unknown(n):return node(('unknown',n))
def plus(a,b):
 if a==z:return b
 if b==z:return a
 return node(('add',min(a,b),max(a,b)))
def times(a,b):
 if a==z or b==z:return z
 if a==one:return b
 if b==one:return a
 return node(('multiply',min(a,b),max(a,b)))
def neg(a):return times(negone,a)
def summ(a):
 ans=z
 for q in a:ans=plus(ans,q)
 return ans
from functools import lru_cache
@lru_cache(None)
def polynomial(e):
 if e.is_Rational:return constant(e)
 if e.is_Symbol:return unknown(str(e))
 if e.is_Add:return summ(polynomial(q) for q in e.args)
 if e.is_Mul:
  ans=one
  for q in e.args:ans=times(ans,polynomial(q))
  return ans
 if e.is_Pow:
  b,k=e.args;k=int(k);assert k>=0;ans=one;b=polynomial(b)
  while k:
   if k&1:ans=times(ans,b)
   k//=2
   if k:b=times(b,b)
  return ans
 raise AssertionError(e)
def rational(e):
 e=sp.cancel(e);num,den=sp.fraction(e);coef,factors=sp.factor_list(den,*syms);ans=times(constant(1/coef),polynomial(num))
 for f,k in factors:
  key=str(sp.expand(f))
  if key not in units:units[key]={'name':f'inverse_{len(units)}','factor':sp.expand(f),'node':polynomial(sp.expand(f))}
  inv=unknown(units[key]['name'])
  for _ in range(k):ans=times(ans,inv)
 return ans
def expr(s):return rational(sp.sympify(s,locals=loc))
def rowmat(v,A):return [summ(times(v[i],A[i][j]) for i in range(len(v))) for j in range(len(A[0]))]
def mm(A,B):return [rowmat(r,B) for r in A]
def matvec(A,v):return [summ(times(a,b) for a,b in zip(row,v)) for row in A]
def scale(c,v):return [times(c,a) for a in v]
def addrows(*rows):return [summ(row[j] for row in rows) for j in range(len(rows[0]))]
eye=[[constant(int(i==j)) for j in range(6)] for i in range(6)];g,ii,p,q,ss,c,o=[unknown(n) for n in names];alpha=addrows(eye[0],scale(p,addrows(eye[1],scale(negone,eye[3]))),scale(q,addrows(eye[4],scale(negone,eye[5]))))
A=[[expr(e) for e in row] for row in fam['A']];T=[[expr(e) for e in row] for row in fam['T']];B=mm(A,[eye[j] for j in [0,1,4]]);Z=mm(A,[alpha,eye[3],eye[5]]);h=expr(fam['h']);aB=rowmat(alpha,B);aZ=rowmat(alpha,Z);aZB=rowmat(aZ,B);ginv=rational(1/loc['g'])
K=[scale(ginv,addrows(scale(times(constant(3),h),eye[0]),scale(times(constant(2),ii),eye[1]),scale(constant(-2),eye[4]),scale(negone,B[3]),scale(constant(-2),aZB),scale(times(constant(2),ii),aB))),scale(constant(-3),eye[0]),scale(constant(-3),eye[0]),addrows(scale(negone,eye[0]),scale(constant(-2),alpha)),addrows(scale(constant(-2),eye[1]),scale(constant(-2),aB)),addrows(scale(negone,eye[1]),scale(negone,eye[3]),scale(constant(-2),aZ))]
v=[one]+[expr(rat['beta_over_beta0'][f'beta{j}']) for j in range(1,6)];kv=matvec(K,v);y=addrows(v,kv);ty=matvec(T,y)
equations=[{'name':f'terminal_{j}','root_node':summ([y[j],neg(times(x,ty[j])),neg(times(x,v[j]))])} for j in range(6)]
equations.append({'name':'empty_Z_minus_B','root_node':summ(times(plus(alpha[j],neg(eye[0][j])),kv[j]) for j in range(6))})
for unit in units.values():equations.append({'name':f"unit_{unit['name']}",'root_node':plus(times(unit['node'],unknown(unit['name'])),negone)})
normalizer=unknown('normalizer');equations.append({'name':'root_normalization','root_node':plus(times(normalizer,plus(one,neg(times(x,v[2])))),negone)})
gout=summ([one,x,times(constant(2),times(times(x,x),normalizer))])
constants=dict(zip(syms,[sp.Rational(cert['center_jet_degree8'][n][0]) for n in names]));unitconditions=[]
for unit in units.values():
 value=unit['factor'].subs(constants);assert value!=0;unitconditions.append({'unknown':unit['name'],'factor':str(unit['factor']),'factor_constant':str(value),'inverse_constant':str(1/value)})
out={'title':'Full G(3,3) finite polynomial system','scope':'Polynomial lift of the exact seven-parameter full graph certificate. The author exact-Q Hensel check proves the selected rational branch exists.','parameter':'x','unknowns':names+[u['name'] for u in units.values()]+['normalizer'],'arithmetic_circuit_semantics':'Nodes are evaluated in order; rational leaves are exact coefficients; parameter and unknown leaves name x or a listed unknown; add/multiply reference earlier zero-based node IDs. Set every equation root to zero.','nodes':nodes,'equations':equations,'G_root_node':gout,'branch_conditions_mod_x5':{n:cert['center_jet_degree8'][n][:5] for n in names},'candidate_center_degree8':cert['center_jet_degree8'],'unit_inverse_conditions':unitconditions,'normalizer_constant':1,'source_files':['eight-parameter-matrix-closure.json','eight_parameter_beta_elimination.json','seven_parameter_full_system_certificate.json'],'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-start}
(P/'full_seven_parameter_polynomial_system.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'unknowns':len(out['unknowns']),'equations':len(equations),'units':unitconditions,'nodes':len(nodes),'bytes':(P/'full_seven_parameter_polynomial_system.json').stat().st_size,'sha256':hashlib.sha256((P/'full_seven_parameter_polynomial_system.json').read_bytes()).hexdigest(),'seconds':time.monotonic()-start},indent=2))
