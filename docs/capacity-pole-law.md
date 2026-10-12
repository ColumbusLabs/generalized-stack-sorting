# An inverse-square law for physical-capacity poles

This is a written analytic proof using a standard saddle-node mechanism. Read [the physical-capacity recurrence](capacity-recursion.md) and [the pole/interlacing preliminaries](capacity-growth.md) first. The analytic argument is outside the Lean certificates.

## Theorem

For the physical-capacity generating functions F_H from the reviewed height
recursion, let rho_H be their positive dominant poles. Write t for the root
of 6t^3+2t^2-5t+1=0 in (0,1/3), and put

    rho=t(1-3t)/[(1+t)(1-2t-2t^2)],
    L=1+t, K=t/(rho L), d=1-2t^2,
    A=[K(K-1)/rho-2rho K^3 L^2]/d,
    B=(1-2t^3)/(K d).

Then A,B>0 and the asymptotic is

    rho_H = rho + pi^2/(A B H^2) + o(H^-2).

Equivalently, the exponential growth constants obey

    lambda-lambda_H ~ pi^2/(rho^2 A B H^2).

Numerically pi^2/(AB)=3.246197810318.... This number is obtained from the map's
derivatives, not inferred by fitting the finite counts.

## 1. The positive map and its global orbit

Use y=(a,b)=(F-1,k-F), with seed y_0=(0,0). Define

    G_x(a,b) = ( x(1+a+b)/(1-x(1+a+b)),
      x(a+3b)/[(1-x(1+2a+4b))(1-x(1+a+b))] ).

It is analytic and componentwise increasing in x,a,b on the positive domain

    Omega_x = {(a,b)>=0: x(1+2a+4b)<1}.

It has nonnegative Taylor coefficients. Its orbit from zero is increasing
until it exits Omega_x. At x=rho, the positive fixed point is

    y*=(t,t^2/(1-3t)).

The orbit from zero is strictly below y* and converges to y*. To check the
last assertion, monotonicity bounds it by y*, and a limit is a fixed point
(the relevant denominators are bounded away from zero below y*). Every
nonnegative fixed point has a=t' in (0,1/3), b=t'^2/(1-3t'), and

    x=t'(1-3t')/[(1+t')(1-2t'-2t'^2)].

This expression has its unique maximum rho at t'=t, as checked by its
explicit derivative. Thus y* is the only nonnegative fixed point at rho,
and there is none for x>rho.

For x>rho, the orbit exits Omega_x in finite time. Otherwise its increasing
coordinates remain bounded by the defining inequality for Omega_x. A limit
on its boundary would make the next iterate unbounded, contradicting this
bound; an interior limit would be a forbidden fixed point.

## 2. Linear and quadratic coefficients

It is convenient to compute in the linearly equivalent coordinates (k,f),
where

    T_x(k,f)=((1+x-4xk+2xf)^(-1),(1-xk)^(-1)).

At (x,k,f)=(rho,K,L), its Jacobian is

    J=[[4rho K^2,-2rho K^2],[rho L^2,0]].

The critical equation implies that its eigenvalues are 1 and r=2t^2 in (0,1).
Use right and left eigenvectors

    v=(1,rho L^2),   ell=(1,-2rho K^2)/d,

so ell.v=1. Then A=ell.T_x and B=ell.D^2T[v,v]/2 give exactly the displayed
formulae. In (a,b) coordinates the right eigenvector is

    v_+=(rho L^2,1-rho L^2),

whose entries are positive. The left eigenvector is

    ell_+=(1/2,1/d),

also positive. Their pairing is 1. Positivity of A and B follows directly
from the nonnegative derivatives of G, strict positivity of ell_+, and a
nonzero parameter/quadratic derivative in the positive direction v_+.

Choose a complementary stable eigenvector and its dual coordinate w. Let
z=ell_+.(y-y*) be the center coordinate. In these fixed linear coordinates,
with delta=x-rho, Taylor expansion gives, uniformly near zero,

    z' = z+A delta+B z^2
         +O(|z|^3+delta |z|+delta^2+|z w|+w^2+delta |w|),
    w' = r w + O(delta+z^2+|z w|+w^2).

The absence of a linear w term in z' follows from ell_+ J=ell_+.

## 3. Quadratic tracking on the incoming critical orbit

At delta=0 the incoming orbit has y_n-y* componentwise negative. Since
ell_+ is strictly positive, equivalence of norms on that negative cone gives
|w_n|<=C|z_n|. Also z_n<0 increases to zero. The first Taylor expansion then
implies

    z_(n+1)=z_n+O(z_n^2),

so z_(n+1)/z_n tends to 1. The second gives

    |w_(n+1)| <= r |w_n|+C z_n^2

once the neighborhood is small, after absorbing the mixed terms by slightly
increasing r to some r_1<1. Choose eta>0 with r_1/(1-eta)^2<1. For all
sufficiently large n, |z_(n+1)| >= (1-eta)|z_n|. Iterating the stable inequality
and summing the resulting geometric series gives

    |w_n|=O(z_n^2).

Indeed z_(n-j)^2 <= z_n^2/(1-eta)^(2j), and the initial stable term divided by
z_n^2 tends to zero by the same ratio. This explicitly excludes approach
along a pure stable direction; positivity of the incoming cone was used.

## 4. A uniform invariant tracking strip

Fix one small coordinate box first, and choose a Taylor-bound constant C_0
valid throughout that box, independently of M. In particular the stable
remainder satisfies

    |w'| <= r|w|+C_0(delta+z^2+|z w|+w^2).

Let C_in be a fixed constant in the critical-orbit bound from Section 3 for
all sufficiently late iterates. Choose M strictly larger than both 2C_in and
4C_0/(1-r). Only after M is fixed choose epsilon>0 sufficiently small. In the
strip |w|<=M(delta+z^2), |z|<=epsilon, 0<=delta<=epsilon^2, require
2M epsilon^2<=epsilon, so |w|<=epsilon and the fixed Taylor box applies.

The center expansion bounds the coefficient of its remainder relative to
h=delta+z^2 by

    C_0[2epsilon+epsilon^2+M epsilon+2M^2 epsilon^2+M epsilon^2].

Shrink epsilon until this is at most 1. Then

    |z'-z| <= C_1 h,   C_1=max(A,B)+1,
    delta+(z')^2 >= (1-2C_1 epsilon)h.

Here C_1 no longer depends on M. The stable bound gives

    |w'| <= [(r+2C_0 epsilon)M+C_0]h.

Shrink epsilon again so that

    r+C_0/M+2(C_0+C_1)epsilon < 1.

It follows that |w'|<=M(delta+(z')^2). This proves invariance of the same
strip for every step until z leaves the neighborhood. All constants are
chosen in the order: fixed Taylor box and C_0; critical-orbit bound C_in;
M; then epsilon. There is no choice of M depending on a subsequent
M-dependent Taylor constant.

After epsilon is fixed, choose one sufficiently late critical iterate N with
-epsilon/2<z_N(0)<0. Its stable coordinate obeys the strict margin

    |w_N(0)| <= C_in z_N(0)^2 < (M/2)z_N(0)^2.

The iterate N is finite and fixed as delta tends to zero. Its negative center
coordinate is nonzero. Continuity of these finitely many iterates therefore
puts the perturbed orbit at time N inside the SAME M-strip, with negative
center coordinate, for all sufficiently small positive delta. For example,
the ratio |w_N(delta)|/(delta+z_N(delta)^2) remains below 3M/4. No enlargement
of the invariant strip is used. The incoming N steps are bounded independently
of delta.
Inside the strip the first expansion now reduces to the scalar inequalities

    (A-C epsilon)delta+(B-C epsilon)z^2
       <= z'-z <=
    (A+C epsilon)delta+(B+C epsilon)z^2.

Take epsilon small enough that all four coefficients are positive.

## 5. Counting discrete passage steps

For q(z)=alpha delta+beta z^2 with fixed positive alpha,beta, q changes by a
relative O(epsilon) during any step of length O(delta+z^2) in |z|<=epsilon.
This follows by expanding q(z+s)-q(z)=2beta z s+beta s^2 and using
|s|<=C(delta+z^2). Therefore summing integrals of 1/q over the consecutive
steps bounds the number of steps between the corresponding integrals, with
multiplicative factors 1+O(epsilon). The scalar inequalities in Section 4 give
upper and lower bounds using alpha=A±Cepsilon and beta=B±Cepsilon.

For any fixed negative entry point and fixed positive exit point,

    sqrt(delta) * integral dz/(alpha delta+beta z^2)
         tends to pi/sqrt(alpha beta).

The first/last overshooting steps contribute only O(1) steps for fixed
epsilon. Taking delta down to zero and then epsilon down to zero yields

    N_pass(delta) ~ pi/sqrt(A B delta).

This is a discrete sum comparison; it does not identify the recurrence with
an ODE without an error bound.

## 6. Entry and exit outside the bottleneck

For fixed epsilon the entry time is bounded uniformly as delta tends to zero,
by the finite-iterate continuity used above.

At the positive exit z=epsilon, the tracking strip gives

    y-y*=epsilon v_+ + O(epsilon^2+delta).

For small epsilon and delta this is componentwise at least
(epsilon/2)v_+. Start a comparison orbit at y*+(epsilon/2)v_+ at x=rho.
The nonnegative Taylor coefficients of G about the positive point y* imply
G_rho(y*+s v_+) >= y*+s v_+, with strict inequality in a component; the
quadratic term is nonzero. Its iterates therefore increase. They cannot
remain in Omega_rho forever, since a bounded limit would be a fixed point
strictly above y*, while a boundary limit is impossible as before. Thus this
comparison orbit exits in finitely many steps, depending on epsilon only.
Monotonicity in x and y bounds the actual post-bottleneck exit time by the
same finite number. Consequently the total positive-orbit lifetime satisfies

    N(rho+delta) ~ pi/sqrt(A B delta).

## 7. Translating lifetime into poles

Let kappa_0=infinity and, for h>=1, let kappa_h be the first positive pole
of k_h. The pole analysis gives kappa_h decreasing to rho. Here is the exact
lifetime convention and induction.

Call h steps successful when y_1,...,y_h are finite and nonnegative, obtained
by applying G only to inputs in Omega_x. Step zero is always successful.
Suppose h-1 steps are successful, equivalently 0<x<kappa_(h-1). On this
interval the h-th k-denominator

    Q_h(x)=1-x(1+2a_(h-1)(x)+4b_(h-1)(x))

is strictly decreasing and has its unique zero at kappa_h. The other
denominator is positive whenever Q_h is positive, by a,b>=0. Hence the h-th
step is successful exactly when x<kappa_h. This proves by induction that
h steps are successful if and only if 0<x<kappa_h; it does not rely on
arbitrary rational continuations past an earlier pole.

Define N(x)=max{h>=0: x<kappa_h}. This is finite for x>rho. The state y_N is
the first one outside Omega_x (possibly exactly on its boundary); applying
G to it would be the first failed step. In particular, at x=kappa_H,

    N(kappa_H)=H-1.

This is the lifetime counted by Sections 1–6, including at a zero denominator.
Applying the passage asymptotic along delta=kappa_H-rho therefore gives

    H-1 ~ pi/sqrt(A B (kappa_H-rho)),
    kappa_H-rho ~ pi^2/(A B H^2).

The previously established interlacing

    kappa_h <= rho_h < kappa_(h-1)

then squeezes rho_h to the same leading asymptotic. Since rho_h tends to rho,
reciprocation gives the claimed growth-constant gap.

## Key proof obligations

- Verify the two eigenvector normalizations and both projected derivatives.
- Check the critical cone bound and the geometric stable-coordinate estimate.
- Check that constants in the invariant strip are chosen without circularity.
- Check the integral/step comparison and the bounded global exit argument.
- Verify the exact lifetime/pole indexing (an O(1) shift is harmless but no
  hidden second bottleneck is allowed).
- No distributional limit for capacity in size-n random permutations follows
  from this pole asymptotic alone; it is established separately in [capacity-typical-height.md](capacity-typical-height.md).
