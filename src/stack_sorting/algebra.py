"""Exact formal-series and polynomial checks of the first-return proof.

These checks do not prove the combinatorial model. The equations are derived
in the proof notes, not inferred from the published coefficients.
"""


def multiply(a, b, order):
    return [sum(a[i]*b[n-i] for i in range(max(0,n-len(b)+1),min(n,len(a)-1)+1))
            for n in range(order+1)]


def first_return_series(order=12):
    if type(order) is not int or not 0 <= order <= 50:
        raise ValueError('order must be an integer from 0 to 50')
    u, b, d, f = [1], [1], [0], [1]
    for n in range(1,order+1):
        common = [b[i]+2*d[i]-(1 if i==0 else 0) for i in range(n)]
        uc = multiply(u, common, n-1)[n-1]
        new_b = multiply(b,b,n-1)[n-1]+uc
        new_d = multiply(b,d,n-1)[n-1]+uc
        factor = [2*b[i]+2*d[i]-(1 if i==0 else 0) for i in range(n)]
        new_u = multiply(u,factor,n-1)[n-1]
        new_f = multiply(u,f,n-1)[n-1]
        u.append(new_u); b.append(new_b); d.append(new_d); f.append(new_f)
    return {'u':u,'b':b,'d':d,'f':f}


def cubic_residual(f):
    """Coefficients through supplied order of 2xf³−(2x+3)f²+(7−x)f−4."""
    order = len(f)-1
    square = multiply(f,f,order)
    cube = multiply(square,f,order)
    return [(2*cube[n-1]-2*square[n-1]-f[n-1] if n else 0)
            -3*square[n]+7*f[n]-(4 if n==0 else 0) for n in range(order+1)]


def elimination_polynomial():
    """Exact bivariate expansion after clearing xu*f=f−1; exponent keys (x,f)."""
    # Expand f(f−1) − xf² − 4(f−1)² + xf(f−1)(2f+1).
    def add(*polynomials):
        result={}
        for polynomial in polynomials:
            for exponent, coefficient in polynomial.items():
                result[exponent]=result.get(exponent,0)+coefficient
        return {key:value for key,value in result.items() if value}
    def mul(a,b):
        result={}
        for (i,j),v in a.items():
            for (k,l),w in b.items():result[i+k,j+l]=result.get((i+k,j+l),0)+v*w
        return result
    f={(0,1):1}; fm1={(0,1):1,(0,0):-1}
    return add(mul(f,fm1), {(1,2):-1},
               {key:-4*value for key,value in mul(fm1,fm1).items()},
               mul({(1,1):1},mul(fm1,{(0,1):2,(0,0):1})))
