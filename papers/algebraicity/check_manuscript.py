#!/usr/bin/env python3
"""Small exact arithmetic checks for the manuscript (Python standard library).

This does NOT replay Lean or prove the all-width MSO argument. It checks the
printed factored Q against its frozen sparse data, its exact scalar blowup,
and the finite-field irreducibility arithmetic. No network, writes to remote
services, floating-point arithmetic, or author verifier imports are used.
"""
from pathlib import Path
import argparse
from functools import reduce
from hashlib import sha256
from math import comb, gcd
import json


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    c = [0] * max(len(a), len(b))
    for i, v in enumerate(a): c[i] += v
    for i, v in enumerate(b): c[i] += v
    return trim(c)


def scale(a, k):
    return trim([k*v for v in a])


def mul(a, b):
    if not a or not b: return []
    c = [0] * (len(a)+len(b)-1)
    for i, u in enumerate(a):
        for j, v in enumerate(b): c[i+j] += u*v
    return trim(c)


def power(a, n):
    b = [1]
    for _ in range(n): b = mul(b, a)
    return b


def factored_display():
    """Coefficients ascending in y, independently transcribed from Appendix A."""
    ym1 = [-1, 1]
    return [
        scale(mul(mul(power(ym1,4),[-18,11]),[-450,783,-414,71]),-1),
        scale(mul(power(ym1,3),[-5508,-7398,41724,-48798,25869,-6811,744]),-2),
        mul(power(ym1,2),[80028,-307764,373266,-174168,94714,-150604,119399,-40638,5103]),
        scale(mul([0,-1,1],[30303,-57006,-60318,204517,-155839,43581,-16536,17661,-7497,999]),-4),
        [0,0,47583,67968,-434593,235008,524094,-671588,251778,-23076,8604,-6912,972],
        scale([0,0,0,2610,24047,4688,-97642,38718,77520,-61902,10260,972],2),
        scale([0,0,0,0]+mul([-5,-10,6],[-20,716,1563,-1458,-1242,864]),-1),
    ]


P = 17

def remainder(a, b):
    a = trim([v % P for v in a]); b = trim([v % P for v in b])
    if not b: raise ZeroDivisionError
    inv = pow(b[-1], P-2, P)
    while a and len(a) >= len(b):
        k = len(a)-len(b); c = a[-1]*inv % P
        for j,v in enumerate(b): a[k+j] = (a[k+j]-c*v) % P
        a = trim(a)
    return a


def gcdmod(a, b):
    while b: a,b = b,remainder(a,b)
    return [v*pow(a[-1],P-2,P) % P for v in a] if a else []


def powmod(a, n, m):
    ans = [1]
    while n:
        if n & 1: ans = remainder(mul(ans,a),m)
        a = remainder(mul(a,a),m); n >>= 1
    return ans


def check(path):
    raw = path.read_bytes(); data = json.loads(raw)
    terms = {(i,j):c for i,j,c in data['terms_x_y_coefficient']}
    assert len(terms) == len(data['terms_x_y_coefficient']) == 69
    assert all(terms.values())
    display = {(i,j):c for i,a in enumerate(factored_display()) for j,c in enumerate(a) if c}
    assert display == terms, 'Printed Appendix A differs from frozen coefficient data'
    assert max(i for i,j in terms) == 6 and max(j for i,j in terms) == 12
    assert {i:c for (i,j),c in terms.items() if j==12} == {4:972}
    assert {i:c for (i,j),c in terms.items() if j==0} == {0:-8100,1:-11016,2:80028}
    assert reduce(gcd,(abs(c) for c in terms.values())) == 1
    assert gcd(781,972) == 1
    C8=[1,1,2,6,24,120,720,5004,38844]
    cp=[power(C8,k) for k in range(13)]
    # Exact full expansion of Q(x,C8+x^9*z), indexed by (x-power,z-power).
    out={}
    for (i,j),c in terms.items():
        for zdegree in range(j+1):
            scalar=c*comb(j,zdegree)
            for d,v in enumerate(cp[j-zdegree]):
                key=(i+9*zdegree+d,zdegree)
                out[key]=out.get(key,0)+scalar*v
    out={k:v for k,v in out.items() if v}
    assert min(i for i,j in out) == 20
    constant={j:c for (i,j),c in out.items() if i==20}
    assert constant == {0:-16*325692*325656,1:16*(325692+325656),2:-16}
    assert constant[1]+2*constant[2]*325692 == -576
    assert data['selected_G_coefficients_through9'] == C8+[325692]
    f=[sum(c*pow(3,i,P) for (i,k),c in terms.items() if k==j)%P for j in range(13)]
    assert f == [5,14,9,10,4,3,14,7,14,3,14,7,5]
    residues={}
    a=[0,1]
    for j in range(1,13):
        a=powmod(a,P,f)
        if j in (4,6,12): residues[str(j)]=a
    assert residues['12']==[0,1]
    for j in (4,6):
        assert gcdmod(f,add(residues[str(j)],[0,-1])) == [1]
    return {
      'status':'PASS', 'equation_sha256':sha256(raw).hexdigest(),
      'display_matches_sparse_json':True, 'terms':69, 'degree_x':6, 'degree_y':12,
      'integer_content':1, 'blowup_x_valuation':20, 'selected_z0':325692,
      'blowup_derivative':-576, 'finite_field':17, 'specialization_x':3,
      'specialized_coefficients':f, 'frobenius_remainders':residues,
      'irreducibility_tests':'Rabin exponents 12, 6, 4; exact degree preserved',
      'scope':'Small arithmetic checks only; no full Lean or MSO proof replay.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--equation',type=Path,default=Path(__file__).with_name('direct-G33-equation.json'))
    parser.add_argument('--report',type=Path,default=Path(__file__).with_name('arithmetic-check.json'))
    args=parser.parse_args()
    report=check(args.equation)
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
