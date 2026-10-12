"""Independent literal relabelling checks and exact completion checks.

No numeric agreement is used as a proof of the quotient theorem.
"""
from pathlib import Path
import sys,itertools,json,time,resource,hashlib
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'src'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from stack_sorting import three_push as nf
from probe_general_hankel import count

def normalized(S):return tuple('Z' if a=='O' else a for a in S)
def states(h,prefix=()):
 if not h:
  if not prefix or prefix[0]=='Z' and (len(prefix)<2 or prefix[1]!='T'):yield prefix
  return
 for a in ('Z','B','T','O'):
  if a=='O' and (not prefix or prefix[-1] not in ('Z','O')):continue
  if not prefix and a!='Z':continue
  if len(prefix)==1 and a=='T':continue
  yield from states(h-1,prefix+(a,))
 if prefix:
  for m in range(2,h+1):yield from states(h-m,prefix+(m,))
def rho(S):
 h=nf.height(S);r=list(range(h+1));pos=1;i=0
 while i<len(S):
  a=S[i]
  if a=='Z':
   j=i+1
   while j<len(S) and S[j]=='O':j+=1
   q=j-i-1
   if q:
    r[pos]=pos+q
    for v in range(pos+1,pos+q+1):r[v]=v-1
   pos+=q+1;i=j
  else:pos+=a if isinstance(a,int) else 1;i+=1
 return r

def literal_orders(S):
 # Independent construction from factor digit language, without nf.expand/decode.
 factors=[]
 for a in S:
  if isinstance(a,int):factors.append([bits for bits in itertools.product((0,1),repeat=a) if 0 in bits])
  else:factors.append([ (v,) for v in {'Z':(0,),'O':(1,),'B':(0,1),'T':(0,1,2)}[a]])
 out=set()
 for choices in itertools.product(*factors):
  digits=sum(choices,());stack=[]
  for j,c in enumerate(digits,1):stack.insert(c,j)
  out.add(tuple(stack))
 return out

start=time.monotonic();literal_cases=0;literal_orders_checked=0;completion_cases=0
for h in range(8):
 for S in states(h):
  r=rho(S);A=literal_orders(S);B=literal_orders(normalized(S))
  assert {tuple(r[a] for a in order) for order in A}==B,(S,normalized(S))
  literal_cases+=1;literal_orders_checked+=len(A)
  if h<=5:
   for m in range(5):
    assert count(S,m)==count(normalized(S),m),(S,m)
    completion_cases+=1
bad={'state':['Z','B','O'],'replacement':['Z','B','Z'],'coefficients_before':[count(('Z','B','O'),m) for m in range(7)],'coefficients_after':[count(('Z','B','Z'),m) for m in range(7)]}
assert bad['coefficients_before']!=bad['coefficients_after']
out={'scope':'Finite corroboration for blockwise O-run normalization; proof is separate.','literal_states_height_through':7,'literal_states':literal_cases,'literal_orders':literal_orders_checked,'completion_initial_height_through':5,'completion_new_input_through':4,'completion_cases':completion_cases,'unreachable_countercontrol':bad,'seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'normal_form_sha256':hashlib.sha256((ROOT/'src/stack_sorting/three_push.py').read_bytes()).hexdigest()}
Path(__file__).with_name('o-run-quotient-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
