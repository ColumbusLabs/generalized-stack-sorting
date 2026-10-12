#!/usr/bin/env python3
"""Plain-Python finite-field review; no computer-algebra factorization calls."""
from pathlib import Path
import json,hashlib,time,resource
ROOT=Path(__file__).resolve().parent;start=time.monotonic();prime=17
resource.setrlimit(resource.RLIMIT_AS,(128<<20,128<<20))
resource.setrlimit(resource.RLIMIT_CPU,(15,15))
for name,row in json.loads((ROOT/'input_manifest.json').read_text()).items():
    assert hashlib.sha256((ROOT/'frozen'/name).read_bytes()).hexdigest()==row['sha256'],name
terms=json.loads((ROOT/'frozen/scalar_G_degree12_x6_candidate.json').read_text())['terms']
cert=json.loads((ROOT/'frozen/G_polynomial_irreducibility_certificate.json').read_text())
assert cert['prime']==17 and cert['specialized_x']==3
def trim(a):
    a=[int(v)%prime for v in a]
    while a and a[-1]==0:a.pop()
    return a
def add(a,b):return trim([(a[k] if k<len(a) else 0)+(b[k] if k<len(b) else 0) for k in range(max(len(a),len(b)))])
def neg(a):return trim([-v for v in a])
def mul(a,b):
    if not a or not b:return []
    out=[0]*(len(a)+len(b)-1)
    for j,v in enumerate(a):
        for k,w in enumerate(b):out[j+k]+=v*w
    return trim(out)
def remainder(a,b):
    a=trim(a);b=trim(b);assert b
    while len(a)>=len(b):
        d=len(a)-len(b);co=a[-1]*pow(b[-1],-1,prime)%prime
        for k,v in enumerate(b):a[d+k]-=co*v
        a=trim(a)
    return a
def gcd(a,b):
    while b:a,b=b,remainder(a,b)
    return trim([v*pow(a[-1],-1,prime) for v in a])
def power(a,n,modulus):
    out=[1]
    while n:
        if n&1:out=remainder(mul(out,a),modulus)
        a=remainder(mul(a,a),modulus);n//=2
    return out
F=[0]*13
for dx,dy,co in terms:F[dy]=(F[dy]+co*pow(3,dx,prime))%prime
assert F==cert['specialized_coefficients_ascending_Y']
assert len(trim(F))==13 and F[-1]==5
leading={dx:co for dx,dy,co in terms if dy==12}
constant={dx:co for dx,dy,co in terms if dy==0}
assert leading=={4:972} and constant=={0:-8100,1:-11016,2:80028}
Y=[0,1];current=Y;checks={}
for k in range(1,13):
    current=power(current,prime,F)
    if k in [4,6,12]:
        assert current==cert['rabin_checks'][str(k)]['frobenius_remainder']
        checks[str(k)]={'frobenius_remainder':current}
        if k<12:
            rem_minus_Y=add(current,neg(Y));assert gcd(F,rem_minus_Y)==[1]
            witness=cert['rabin_checks'][str(k)]
            assert add(mul(witness['bezout_F'],F),mul(witness['bezout_remainder_minus_Y'],rem_minus_Y))==[1]
            checks[str(k)]['gcd_and_explicit_bezout_verified']=True
        else:assert current==Y
# Adversarial controls: a corrupted claimed remainder and a corrupted Bezout fail.
bad=cert['rabin_checks']['4']['frobenius_remainder'].copy();bad[0]=(bad[0]+1)%prime
assert bad!=checks['4']['frobenius_remainder']
w=cert['rabin_checks']['4'];bad=w['bezout_F'].copy();bad[0]=(bad[0]+1)%prime
assert add(mul(bad,F),mul(w['bezout_remainder_minus_Y'],add(checks['4']['frobenius_remainder'],neg(Y))))!=[1]
receipt={'status':'PASS','field_characteristic':prime,'specialization_x':3,'degree_preserved':12,'checks':checks,'x_content_witness':{'leading_Y_coefficient':'972*x^4','constant_Y_coefficient':'-8100-11016*x+80028*x^2','gcd_over_Q_x':1},'conclusion':'Q is irreducible over Q(x); its selected root has algebraic degree exactly 12. The monic minimal polynomial is Q/(972*x^4).','negative_controls':['modified Frobenius remainder','modified Bezout coefficient'],'seconds':time.monotonic()-start,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'irreducibility_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
