#!/usr/bin/env python3
"""Independent arithmetic-circuit evaluation for the full polynomial lift."""
from pathlib import Path
import sys,json,time,hashlib,resource
sys.path.insert(0,str(Path(__file__).with_name('python-packages')))
from flint import fmpq,fmpq_poly as Poly
import sympy as sp
resource.setrlimit(resource.RLIMIT_AS,(512<<20,512<<20));P=Path(__file__).resolve().parent;start=time.monotonic();D=10
data=json.loads((P/'full_seven_parameter_polynomial_system.json').read_text())
def pol(a):return Poly([fmpq(str(v)) for v in a])
def mul(a,b):return (a*b).truncate(D+1)
def inv(a):
 assert a[0];out=[1/a[0]]
 for k in range(1,D+1):out.append(-sum((a[j]*out[k-j] for j in range(1,k+1)),fmpq(0))/a[0])
 return Poly(out)
values={n:pol(v) for n,v in data['candidate_center_degree8'].items()}
def evaluate_expr(e):
 if e.is_Rational:return pol([str(e)])
 if e.is_Symbol:return values[str(e)]
 if e.is_Add:return sum((evaluate_expr(z) for z in e.args),Poly([]))
 if e.is_Mul:
  ans=pol([1])
  for z in e.args:ans=mul(ans,evaluate_expr(z))
  return ans
 if e.is_Pow:
  a,k=e.args;k=int(k);assert k>=0;v=evaluate_expr(a);out=pol([1])
  for _ in range(k):out=mul(out,v)
  return out
 raise AssertionError(e)
for u in data['unit_inverse_conditions']:values[u['unknown']]=inv(evaluate_expr(sp.sympify(u['factor'])))
values['normalizer']=pol([1])
def evaluate_nodes():
 out=[]
 for n in data['nodes']:
  if n[0]=='rational':v=pol([n[1]])
  elif n[0]=='parameter':assert n[1]=='x';v=pol([0,1])
  elif n[0]=='unknown':v=values[n[1]]
  elif n[0]=='add':v=out[n[1]]+out[n[2]]
  elif n[0]=='multiply':v=mul(out[n[1]],out[n[2]])
  else:raise AssertionError(n)
  out.append(v)
 return out
out=evaluate_nodes();normeq=next(e for e in data['equations'] if e['name']=='root_normalization');rootnode=data['nodes'][normeq['root_node']];product=next(data['nodes'][i] for i in rootnode[1:] if data['nodes'][i][0]=='multiply');factornode=next(i for i in product[1:] if data['nodes'][i]!=['unknown','normalizer']);values['normalizer']=inv(out[factornode]);out=evaluate_nodes()
for e in data['equations']:assert not out[e['root_node']].truncate(9),e['name']
g=out[data['G_root_node']];counts=json.loads(Path(__file__).with_name('full-class-counts-through-26.json').read_text())['counts'];assert [str(g[i]) for i in range(D+1)]==[str(v) for v in counts[:D+1]]
result={'status':'PASS','field':'Q','scope':'Exact exported polynomial-circuit residuals through x8 and G coefficients through x10. Formal all-word theorem is reviewed separately.','unknowns':len(data['unknowns']),'equations':len(data['equations']),'circuit_nodes':len(data['nodes']),'residual_verified_degree':8,'G_verified_degree':D,'G_coefficients':[str(g[i]) for i in range(D+1)],'circuit_sha256':hashlib.sha256((P/'full_seven_parameter_polynomial_system.json').read_bytes()).hexdigest(),'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(P/'full_polynomial_circuit_verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
