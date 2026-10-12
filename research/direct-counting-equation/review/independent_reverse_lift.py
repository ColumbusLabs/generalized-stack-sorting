#!/usr/bin/env python3
"""Check that zero five-coordinate equations really imply all seven original ones."""
from pathlib import Path
import sympy as S
import json,hashlib,resource,time
resource.setrlimit(resource.RLIMIT_AS,(512<<20,512<<20))
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
ROOT=Path(__file__).resolve().parent;start=time.monotonic();checks=[]
for name,row in json.loads((ROOT/'input_manifest.json').read_text()).items():
    assert hashlib.sha256((ROOT/'frozen'/name).read_bytes()).hexdigest()==row['sha256'],name
read=lambda name:json.loads((ROOT/'frozen'/name).read_text())
g,i,p,q,s,c,o,x,a,t,u=S.symbols('g i p q s c o x a t u')
parse=lambda v:S.sympify(v,locals={str(z):z for z in (g,i,p,q,s,c,o,x,a,t,u)})
rat=lambda v:parse(v['numerator'])/parse(v['denominator'])
def check(name,expr):
    assert S.cancel(expr)==0,name
    checks.append(name);print(name,'PASS',flush=True)
original=read('seven_scalar_numerators.json')['equations'];six=[rat(row) for row in read('six_parameter_selected_system.json')['equations']]
for k in range(6):check('original_to_six_'+str(k),rat(original[k]).subs(p,-i*q)-six[k])
check('empty_equation_from_p=-iq',rat(original[6]).subs(p,-i*q))
five=read('five_scalar_reduction.json');csol=parse(five['c_elimination']['answer']);coefficient=parse(five['c_elimination']['coefficient'])
check('F2_recovered_by_c',six[2]-coefficient*(c-csol))
check('F0_after_c',six[0].subs(c,csol)-rat(five['last_equation']))
combined={'F1-oF0':six[1]-o*six[0],'F3':six[3],'F5-iF3':six[5]-i*six[3],'short4':six[4]-(i*o-1/q)*six[0]-i*(six[1]-o*six[0]),'last':rat(five['last_equation'])}
coord={g:u/(q*t),s:t/q,o:i-a};changed=read('changed_scalar_coordinates.json')['equations']
for name,expr in combined.items():check('invertible_row_combination_'+name,expr.subs(coord,simultaneous=True)-rat(changed[name]))
for expr,goal in [(g*q*q*s,u),(q*s,t),(i-o,a)]:check('coordinate_inverse_'+str(goal),expr.subs(coord,simultaneous=True)-goal)
receipt={'status':'PASS','checks':checks,'logical_use':'On the certified unit-denominator chart, the five zeros and recovered c give F0=F2=0, then F1=F3=F4=F5=0 by these reversible row combinations. Setting p=-iq gives the remaining empty equation.','seconds':time.monotonic()-start,'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'reverse_lift_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
