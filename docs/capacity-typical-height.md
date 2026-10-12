# Typical physical capacity: a mass-conditioned tree bridge

This written probability argument is separate from the Lean enumeration certificate. The probability limit theorem is prior work; the contribution here is its specialization to physical capacity in this stack class.

## Statement

Choose uniformly a sortable permutation of length n, and let C_n be its minimum
physical stack capacity. Let rho, A and B be the critical point and positive
normal-form coefficients defined in the capacity pole-law proof. Put

    beta = sqrt(2/(rho*A*B)) = 2.21664566858859... .

Let e be a standard normalized Brownian excursion on [0,1], and M its maximum.
Then

    C_n/sqrt(n)  ->  beta*M

in distribution, and every positive real moment converges. There are constants
c,C>0 independent of n such that P(C_n>y)<=C exp(-c*y^2/n) for n>=1,y>0.
The same limit holds for maximum drop, because C_n=maxdrop+1.

This is **not** inferred from the inverse-square pole law. The proof below uses
an exact height/size distribution correspondence and a published conditioned
multitype branching-process theorem.

## 1. Exact two-type decorated trees

Write a_H=F_H-1 and b_H=k_H-F_H. The established capacity recursion, including
the temporary physical slot for bypass, is exactly

    (a_0,b_0)=(0,0),
    a_H = G_A(x,a_(H-1),b_(H-1)),
    b_H = G_B(x,a_(H-1),b_(H-1)),

where

    G_A(x,a,b)=x(1+a+b)/(1-x(1+a+b)),
    G_B(x,a,b)=x(a+3b)/[(1-x(1+2a+4b))(1-x(1+a+b))].

These positive rational specifications have the following literal interpretation.
An A-vertex has an ordered nonempty list of m slots. Each slot is empty or holds
one A-child or one B-child. The vertex has token mass m.

A B-vertex has an ordered prefix of p slots, one distinguished central child,
and an ordered suffix of q slots. Each prefix slot is empty or holds an A-child
in one of two colours or a B-child in one of four colours. The central child is
an A-child or a B-child in one of three colours. Each suffix slot is empty or
holds an A-child or B-child without a colour. Its token mass is 1+p+q. Children
are ordered by these slots, prefix then central child then suffix. Colours and
empty slots are retained as decoration data.

Every vertex has strictly positive token mass. Tree height means the number of
A/B vertices along a longest root-to-vertex path. Induction on H now proves that
(a_H,b_H) enumerate these trees of height at most H, by total token mass, according
to root type. There are finitely many decorated trees of each mass: their vertex
count and total slot count are bounded by that mass.

Thus for n>=1 the uniform size-n A-rooted decorated tree has exactly the same
height distribution as C_n:

    P(C_n<=H)=[x^n]a_H/[x^n]a.

Only equality of these cumulative counts is needed. We do not claim an extra
explicit bijection assigning a metric tree to each permutation.

## 2. Removing the size-conditioning mismatch

Set tau=(tau_A,tau_B)=(a(rho),b(rho)). For each A/B vertex with decoration mass m,
append m new sterile type-C leaf children after its existing ordered A/B children.
Keep the original decoration as a mark while defining this expansion.

The expanded tree has exactly n C-vertices if and only if the original decorated
tree has total token mass n. Moreover its usual edge-height is **exactly** the
original A/B node-height: a deepest A/B vertex is at depth H-1 and has at least
one C-child at depth H. No new longer path can occur.

For a decoration of a type-i vertex with m tokens and ordered A/B offspring
j_1,...,j_r, assign probability

    rho^m * product_l tau_(j_l) / tau_i.

Summing over decorations gives 1 because G_i(rho,tau)=tau_i. Identical offspring
words arising from distinct decorations receive their summed probabilities.
After forgetting marks the expanded object is an ordinary three-type ordered
Bienayme tree. Its offspring generating functions are

    phi_i(s_A,s_B,s_C)=G_i(rho*s_C,tau_A*s_A,tau_B*s_B)/tau_i, i=A,B,
    phi_C=1.

The product of the marked offspring probabilities over a finite A-rooted tree
telescopes to rho^n/tau_A. Hence conditioning on #C=n gives the uniform distribution
on decorated trees of token mass n before forgetting the marks. Forgetting marks
does not alter either height or #C. This proves the required conditioning bridge;
ordinary conditioning on the number of A/B vertices would be incorrect.

## 3. Verification of the published theorem's hypotheses

Let t be the unique root of 6t^3+2t^2-5t+1=0 in (0,1/3). As in the critical-point
calculation already established for the capacity recursion,

    rho=t(1-3t)/[(1+t)(1-2t-2t^2)],
    tau_A=t, tau_B=t^2/(1-3t).

Both tau coordinates are positive. At (rho,tau), the two denominators of G are
strictly positive; explicitly they are 1/(1+t) and
(1-3t)/(1-2t-2t^2). Consequently the three offspring generating functions are
finite in a neighbourhood of (1,1,1), giving exponential offspring moments.

Let D=diag(tau_A,tau_B) and J=G_y(rho,tau). The A/B mean matrix is

    M=D^(-1)*J*D.

All its entries are positive. Direct substitution, or the equivalent Jacobian
calculation in the pole-law proof, gives J eigenvalues 1 and 2t^2. Therefore M
is irreducible and critical. The full three-type mean matrix has block form

    [ M  m ]
    [ 0  0 ],       m_i=rho*G_(i,x)(rho,tau)/tau_i >0.

Its extra component is sterile and hence strictly subcritical. An A-vertex can
have no A/B children with positive probability. It can also have two A-children
with positive probability (two occupied slots). The model is nondegenerate.
Every n>=1 is admissible: one A-vertex with n empty slots has mass n. In
particular no subsequence qualification is needed in this application.

Apply Addario-Berry, Beltran, Stufler and Thevenin, *Scaling limits of multitype
Bienayme trees*, arXiv:2507.23241v2, Theorem 1.5 (the reducible case), equivalently
Theorem 9 of the AofA 2026 extended abstract. This theorem gives a rooted Brownian
CRT limit and a uniform height tail bound when a regular critical irreducible
core has attached subcritical types and conditioning fixes a nonnegative linear
combination of the type counts. Use the weight vector (0,0,1).

Primary sources, inspected 9 October 2026:
- Full theorem and conventions: https://arxiv.org/html/2507.23241v2#S1.SS4
  (version 2 dated 12 June 2026; rooted topology in Section 1.2.6).
- Published extended abstract, 13 July 2026:
  https://doi.org/10.4230/LIPIcs.AofA.2026.4

## 4. Exact normalization

Let p be the positive left 1-eigenvector of M, normalized by p_A+p_B=1, and q
its positive right 1-eigenvector, normalized by p.q=1. Define

    mu = sum_i p_i*m_i,
    sigma^2 = sum_(i,j,k) p_i*q_j*q_k *
              (tau_j*tau_k/tau_i)*G_(i,y_j y_k)(rho,tau),

where all indices range over A,B. The extended left eigenvector is (p_A,p_B,mu).
The theorem's scaling constant is sigma*sqrt(mu)/2. Thus the capacity limit
factor is beta=2/(sigma*sqrt(mu)). The sterile leaves contribute to conditioning
mass, not to the branching variance along the critical core.

To compare with the already derived pole-law constant, put ell=p*D^(-1) and
v=D*q, so ell.v=1. The center coefficients for the positive map are

    A_*=ell.G_x,      B_*=ell.G_yy[v,v]/2.

Then mu=rho*A_* and sigma^2=2*B_*. The product A_*B_* is unchanged by rescaling
the dual Perron eigenvectors and by an invertible linear coordinate change.
Consequently it is the same AB used in the pole-law proof, proving

    beta=2/sqrt(2*rho*A*B)=sqrt(2/(rho*A*B)).

This is an independent normalization calculation, not a fit to the pole data.
Numerical diagnostics from the explicit derivatives are

    rho = 0.13387906715106272529...,
    mu = 1.53039374801096034587...,
    sigma^2 = 0.53194196757744679007...,
    beta = 2.21664566858859345013... .

## 5. Height convergence and moments

Height from the root is a continuous functional for rooted Gromov--Hausdorff
convergence. The Brownian CRT coded by the standard excursion has root-height
M=max e. The exact expansion in Section 2 therefore transfers the published
CRT limit to C_n, yielding the stated distributional limit.

The theorem also supplies a bound of the form
C exp(-c*y^2/n)+C exp(-c*y). Here C_n<=n deterministically, since each vertex on
a maximal A/B path has mass at least one. For y<=n the second term is bounded by
the first after adjusting constants, and for y>n the probability is zero. This
gives the displayed sub-Gaussian bound. Integrating the tails yields uniform
integrability of every fixed positive power of C_n/sqrt(n), hence convergence
of all positive real moments.

## Assessment

The mass-conditioning obstacle is resolved by a concrete sterile-leaf encoding
and a directly matching published theorem. The probability machinery and the
Brownian universality class are established theory. The class-specific result
is the capacity distribution, its exact normalization, and its connection to
the already derived capacity family. This is a useful theorem specialization,
not a new general invariance principle.
