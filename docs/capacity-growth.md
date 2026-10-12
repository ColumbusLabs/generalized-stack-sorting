# Fixed-capacity poles and growth constants

This written proof develops the physical-capacity recursion in [capacity-recursion.md](capacity-recursion.md). The sharper inverse-square convergence law is in [capacity-pole-law.md](capacity-pole-law.md). The analytic arguments are outside the Lean certificates.

## 1. Positive recursion and poles

Put a_h=F_h-1 and b_h=k_h-F_h. The height recursion is equivalently

    a_0=b_0=0,
    a_h=x(1+a_(h-1)+b_(h-1))/(1-x(1+a_(h-1)+b_(h-1))),
    b_h=x(a_(h-1)+3b_(h-1)) /
        [(1-x(1+2a_(h-1)+4b_(h-1)))
         (1-x(1+a_(h-1)+b_(h-1)))].

This map has nonnegative power-series coefficients and is increasing in its
arguments wherever the denominators are positive. The orbit from (0,0) is
componentwise increasing. The rational functions count the already established
bounded operation paths; the signs in the reduced k,F recursion are not signed
combinatorial weights.

Let kappa_h be the radius of k_h and rho_h the radius of F_h, h>=1. Initially
kappa_1=rho_1=1. At each later step, the denominator of k_h is

    1-x(1+2a_(h-1)+4b_(h-1)),

and that of F_h is 1-x(1+a_(h-1)+b_(h-1)). Each strictly decreases from 1 to a
negative value before the preceding positive pole. The subtracted series has
nonnegative coefficients, and it diverges at the previous k-pole. Thus the
first positive zero exists, is unique, and has a strictly negative derivative;
the new singularity is a simple pole, not a removable zero. Comparison gives

    kappa_h < rho_h < kappa_(h-1)  (h>=2).

The first inequality uses a_(h-1)>0; the second follows because k_(h-1) diverges.
All these functions are analytic before their first positive pole by induction:
for complex z with |z| less than the positive zero, coefficientwise positivity
bounds the modulus of each subtracted series strictly below 1.

F_h has no other singularity of modulus rho_h. For h>=2 the denominator is
1-x k_(h-1)(x), whose subtracted series has positive coefficients at both x and
x^2. Equality in the triangle inequality at a putative complex zero therefore
forces its argument to be zero. The preceding k-radius is strictly larger.
The h=1 case is immediate. Consequently

    [x^n] F_h(x) ~ C_h rho_h^(-n),
    C_h = 1 / (1 + rho_h^2 k'_(h-1)(rho_h)) > 0.

This is a standard simple-pole calculation, not a new asymptotic method.

## 2. Limit of the fixed-capacity growth constants

Let tau be the unique root in (0,1/3) of

    6 tau^3 + 2 tau^2 - 5 tau + 1 = 0,

and let

    rho = tau(1-3tau)/[(1+tau)(1-2tau-2tau^2)].

Numerically tau=0.239382793737560..., rho=0.133879067151063..., and
lambda=1/rho=7.46942760567.... These values concern the known cubic branch.

At x=rho the positive recursion has a fixed point

    a*=tau, b*=tau^2/(1-3tau).

The increasing orbit from zero is bounded above by this fixed point, so every
kappa_h>=rho. Suppose their decreasing limit exceeded rho and choose x strictly
between. Then every iterate is positive and defined. Positivity of the next
k-denominator and b>=0 bound k_h by (1+x)/(2x). Hence the orbit converges to a
finite nonnegative fixed point. Every such fixed point satisfies

    a=t in (0,1/3), b=t^2/(1-3t),
    x=t(1-3t)/[(1+t)(1-2t-2t^2)].

The right side has its unique maximum rho in that interval: differentiation
has numerator proportional to (t-1)(6t^3+2t^2-5t+1), and the cubic is strictly
decreasing on (0,1/3). This contradicts x>rho. Therefore

    rho_h decreases strictly to rho,
    lambda_h=1/rho_h increases strictly to lambda.

For each fixed h, the fraction of length-n sortable permutations that fit in
capacity h decays exponentially, up to the ordinary n^(3/2) factor below.
This proves escape from every fixed capacity; it does not determine the
correct growing scale of typical capacity.

## 3. An elementary quantitative bound

Let A_n be the unbounded sortable count. Concatenating sortable blocks as a
direct sum gives A_h^q distinct inputs of length qh sortable with capacity h;
append an increasing block to obtain every residue class of lengths. Thus
lambda_h >= A_h^(1/h).

For the already-known cubic, t=f-1 satisfies t=x Phi(t), where

    Phi(t)=(1-t-4t^2-2t^3)/(1-3t)
          =1+2t+2t^2+4t^3+12t^4+36t^5+... .

The standard smooth implicit-function/singularity-transfer calculation gives

    A_n ~ c rho^(-n) n^(-3/2),
    c=sqrt(Phi(tau)/(2*pi*Phi''(tau)))>0.

Its hypotheses are visible here: nonnegative aperiodic coefficients, tau<1/3,
Phi(tau)=tau Phi'(tau), and Phi''(tau)>0. The corresponding standard reference
is Flajolet and Sedgewick, *Analytic Combinatorics*, smooth implicit-function
schema and square-root transfer:
https://algo.inria.fr/flajolet/Publications/book.pdf

It follows that

    0 <= log(lambda/lambda_h)
       <= [(3/2) log h - log c + o(1)]/h.

This is a routine consequence of block concatenation and the known cubic.
It is useful as a rigorous baseline, not as the headline research target.


The unbounded coefficient asymptotic is already recorded in [OEIS A393395](https://oeis.org/A393395), credited to Vaclav Kotesovec. It is not claimed as new here.
