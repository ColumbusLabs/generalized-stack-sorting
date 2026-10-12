#!/usr/bin/env python3
"""Exact rational evaluation/Hensel certificate for the seven-parameter full graph system."""
from pathlib import Path
from functools import lru_cache
import sys,json,time,resource,hashlib
sys.path.insert(0,str(Path(__file__).with_name('python-packages')))
from flint import fmpq,fmpq_poly as Poly,fmpq_mat as Mat
import sympy as sp
resource.setrlimit(resource.RLIMIT_AS,(768<<20,768<<20));root=Path(__file__).resolve().parent;start=time.monotonic();D=8;N=7
family=json.loads(Path(__file__).with_name('eight-parameter-matrix-closure.json').read_text());betadata=json.loads((root/'eight_parameter_beta_elimination.json').read_text());base=json.loads(Path(__file__).with_name('six-transfer-candidate-degree8.json').read_text());az=json.loads((root/'alpha_z_degree8.json').read_text())
names=['g','i','p','q','s','c','o'];symbols=sp.symbols(' '.join(names));loc={str(v):v for v in symbols};loc['w']=sp.Rational(3,2)*loc['o']
def pol(a):return Poly([fmpq(str(v)) for v in a])
def mul(a,b):return (a*b).truncate(D+1)
def invpol(a):
 assert a[0]!=0
 out=[1/a[0]]
 for k in range(1,D+1):out.append(-sum((a[i]*out[k-i] for i in range(1,k+1)),fmpq(0))/a[0])
 return Poly(out)
rawg=pol(base['matrices']['B'][4][0]);rawi=pol(base['matrices']['B'][4][4]);rawp=pol(az[1]);rawq=pol(az[4]);rawd=pol(base['matrices']['B'][3][0]);raws=mul(-2*mul(rawq,rawd)-Poly([1]),invpol(2*(rawp+mul(rawg,mul(rawq,rawq)))))
center=[rawg,rawi,rawp,rawq,raws,pol(base['matrices']['B'][2][4]),pol(base['matrices']['T'][1][2])]
class Dual:
 def __init__(self,v=None,d=None):self.v=Poly([]) if v is None else v;self.d=[Poly([]) for _ in range(N)] if d is None else d
 def __add__(a,b):
  if not isinstance(b,Dual):b=Dual(Poly([b]))
  return Dual(a.v+b.v,[x+y for x,y in zip(a.d,b.d)])
 __radd__=__add__
 def __neg__(a):return Dual(-a.v,[-z for z in a.d])
 def __sub__(a,b):return a+-b
 def __rsub__(a,b):return -a+b
 def __mul__(a,b):
  if not isinstance(b,Dual):b=Dual(Poly([b]))
  return Dual(mul(a.v,b.v),[mul(x,b.v)+mul(a.v,y) for x,y in zip(a.d,b.d)])
 __rmul__=__mul__
 def inv(a):
  assert a.v[0]!=0,'Nonunit denominator';v=invpol(a.v);vv=mul(v,v);return Dual(v,[-mul(z,vv) for z in a.d])
 def __truediv__(a,b):
  if not isinstance(b,Dual):b=Dual(Poly([b]))
  return a*b.inv()
vals={s:Dual(center[k],[Poly([int(k==j)]) for j in range(N)]) for k,s in enumerate(symbols)}
@lru_cache(None)
def ev(e):
 if e.is_Rational:return Dual(Poly([fmpq(str(e))]))
 if e.is_Symbol:return vals[e]
 if e.is_Add:return sum((ev(a) for a in e.args),Dual())
 if e.is_Mul:
  out=Dual(Poly([1]))
  for a in e.args:out=out*ev(a)
  return out
 if e.is_Pow:
  a,k=e.args;k=int(k);v=ev(a)
  if k<0:v=v.inv();k=-k
  out=Dual(Poly([1]))
  while k:
   if k&1:out=out*v
   k//=2
   if k:v=v*v
  return out
 raise AssertionError(e)
def expr(s):return ev(sp.sympify(s,locals=loc))
def dot(a,b):return sum((x*y for x,y in zip(a,b)),Dual())
def rowmat(v,A):return [dot(v,[row[j] for row in A]) for j in range(len(A[0]))]
def mm(A,B):return [rowmat(row,B) for row in A]
def matvec(A,b):return [dot(row,b) for row in A]
eye=[[Dual(Poly([int(i==j)])) for j in range(6)] for i in range(6)]
g,ii,p,q,ss,c,o=[vals[v] for v in symbols];alpha=[eye[0][j]+p*(eye[1][j]-eye[3][j])+q*(eye[4][j]-eye[5][j]) for j in range(6)]
A=[[expr(e) for e in row] for row in family['A']];T=[[expr(e) for e in row] for row in family['T']];E=[eye[j] for j in [0,1,4]];B=mm(A,E);Z=mm(A,[alpha,eye[3],eye[5]]);h=expr(family['h'])
aB=rowmat(alpha,B);aZ=rowmat(alpha,Z);aZB=rowmat(aZ,B)
K=[[Dual() for _ in range(6)] for _ in range(6)]
for j in range(6):
 K[0][j]=(3*h*eye[0][j]+2*ii*eye[1][j]-2*eye[4][j]-B[3][j]-2*aZB[j]+2*ii*aB[j])/g
 K[1][j]=K[2][j]=-3*eye[0][j]
 K[3][j]=-eye[0][j]-2*alpha[j]
 K[4][j]=-2*eye[1][j]-2*aB[j]
 K[5][j]=-eye[1][j]-eye[3][j]-2*aZ[j]
v=[Dual(Poly([1]))]+[expr(betadata['beta_over_beta0'][f'beta{j}']) for j in range(1,6)]
xx=Dual(Poly([0,1]));kv=matvec(K,v);y=[v[i]+kv[i] for i in range(6)];ty=matvec(T,y)
F=[y[i]-xx*ty[i]-xx*v[i] for i in range(6)]+[dot([alpha[i]-eye[0][i] for i in range(6)],kv)]
res=[str(f.v) for f in F];print('residuals',res,'seconds',time.monotonic()-start,flush=True)
assert all(not f.v for f in F),'Candidate residual does not vanish through x8'
J=[[f.d[j] for j in range(N)] for f in F];JJ=[[z for z in row] for row in J];roworder=list(range(N));colorder=list(range(N));piv=[]
def valuation(v):return next((k for k in range(D+1) if v[k]),D+1)
for k in range(N):
 vv,i,j=min((valuation(JJ[i][j]),i,j) for i in range(k,N) for j in range(k,N));assert vv<=D,('rank deficient',k)
 JJ[k],JJ[i]=JJ[i],JJ[k];roworder[k],roworder[i]=roworder[i],roworder[k]
 for row in JJ:row[k],row[j]=row[j],row[k]
 colorder[k],colorder[j]=colorder[j],colorder[k]
 unit=JJ[k][k].right_shift(vv);inv=invpol(unit)
 for i in range(k+1,N):
  quotient=mul(JJ[i][k].right_shift(vv),inv)
  for j in range(k+1,N):JJ[i][j]=(JJ[i][j]-mul(quotient,JJ[k][j])).truncate(D+1)
  JJ[i][k]=Poly([])
 piv.append({'valuation':vv,'constant_unit':str(unit[0]),'equation_index':roworder[k],'variable':names[colorder[k]]})
print('pivots',piv,flush=True)
# Freeze explicit rational seven-equation definition by matrix recipe, including every center jet.
centerjet={name:[str(center[i][j]) for j in range(D+1)] for i,name in enumerate(names)}
result={'scope':'Exact full seven-parameter graph-system branch certificate; all-word identification uses the assembled graph and boundary proof.','variables':names,'center_jet_degree8':centerjet,'equation_definition':{'terminal':'(I-xT)(I+K)v-xv=0, six scalar equations','empty':'(alpha-e0)K v=0','w_substitution':'3*o/2','v0':1,'v_ratios_source':'eight_parameter_beta_elimination.json','matrix_source':'eight-parameter-matrix-closure.json','K_rows':['(3*h*e0+2*i*e1-2*e4-e3*B-2*alpha*Z*B+2*i*alpha*B)/g','-3*e0','-3*e0','-e0-2*alpha','-2*e1-2*alpha*B','-e1-e3-2*alpha*Z'],'normalization':'beta0=2/(1-x*v2); beta=beta0*v; G=1+x+2*x^2/(1-x*v2)'},'residual_valuation_at_least':D+1,'jacobian_smith_pivots':piv,'jacobian_inverse_pole_order':max(p['valuation'] for p in piv),'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(root/'seven_parameter_full_system_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('center_jet_degree8','equation_definition')},indent=2))
