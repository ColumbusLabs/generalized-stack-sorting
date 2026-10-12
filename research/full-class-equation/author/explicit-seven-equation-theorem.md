# An explicit seven-equation system for unrestricted G(3,3)

The statement below is the assembled mathematical theorem, conditional only on successful verification of the cited finite certificates and the combinatorial reductions. No coefficient fit is used as an all-length premise.

## 1. Result

Let y=(g,i,p,q,s,c,o) be the formal branch of the seven rational equations

\[
\boxed{(I_6-xT)(I_6+K)v-xv=0,\qquad (\alpha-e_0)Kv=0.}                 \tag{1}
\]

The first equality is a six-component column equality. All matrices and the normalized column v are the explicit rational functions of y defined below. Then the ordinary generating function for the actual unrestricted (3,3) permutation class is

\[
\boxed{G(3,3;x)=1+x+\frac{2x^2}{1-xv_2}.}                              \tag{2}
\]

This is a finite algebraic specification, with seven scalar branch unknowns. Clearing denominators gives polynomial equations; all cleared denominators are units on the specified branch. An entirely expanded arithmetic-circuit version is supplied separately. Equation (1) is not a scalar minimal polynomial for G.

The branch is selected by the following coefficients through degree four, in ascending powers of x:

| variable | x^0 | x^1 | x^2 | x^3 | x^4 |
|---|---:|---:|---:|---:|---:|
| g | 12 | 36 | 144 | 756 | 4704 |
| i | 8 | 8 | 28 | 150 | 964 |
| p | -4/9 | 4/9 | 22/27 | 107/27 | 1928/81 |
| q | 1/18 | -1/9 | -5/27 | -26/27 | -484/81 |
| s | 9/2 | 9/2 | 39/2 | 105 | 1305/2 |
| c | 2 | 0 | 0 | -3/2 | -35/2 |
| o | 6 | 6 | 24 | 132 | 840 |

The parameter named g here is an auxiliary matrix entry, not the generating function G.

## 2. Explicit matrix recipe

All vectors e_j below are the six-dimensional coordinate rows, indexed 0 through 5. For matrix row or column selections, use the ordered index list I=(0,1,4). Write E for the 3-by-6 matrix with rows e_0,e_1,e_4. Put

\[
\begin{aligned}
h&=\frac{2ipqs+iq+2p^2s+p-2qs}{2q^2s},\\
z_0&=1+q(h-pg),&z_1&=p+q(i-qg),\\
d&=-\frac1{2q}-s(p/q+qg),&j&=g-(s+pd)/q,\\
e&=pd-sz_0,&f&=qd+\tfrac12-sz_1,\\
k&=h-pg+pj-(p/q)(e-pd)+\frac1{2q},\\
\ell&=i-qg+qj-(p/q)(f-qd)+p/q,\\
a&=(c-\tfrac32+3sz_1)/q,&b&=pa-3sz_0.
\end{aligned}
\]

Define

\[
 A=\begin{pmatrix}0&1&0\\0&0&1\\a&b&c\\d&e&f\\g&h&i\\j&k&\ell\end{pmatrix},\quad
 \alpha=e_0+p(e_1-e_3)+q(e_4-e_5),\quad
 B=AE,\quad Z=A\begin{pmatrix}\alpha\\e_3\\e_5\end{pmatrix}.
\]

Let L=B-Z, C=B[I,I], V=AC^{-1}, W=L[:,(1,4)], and

\[
 P=Z[I,:]V,\quad Q=Z[I,:]W,\quad
 \Delta=\begin{pmatrix}e_1-e_3\\e_4-e_5\end{pmatrix}.
\]

Let f_0=(1,0,0), f_1=(0,1,0), u=-2f_0C^{-1}. The six rows of H_F are

\[
 u,\quad uP-f_0,\quad -3f_0,\quad -f_0,\quad (uP-f_0)P-f_1,\quad -f_1.
\]

The only nonzero rows of H_J are

\[
 (H_J)_3=-2\alpha V,\qquad (H_J)_5=-e_3V-2\alpha ZV.
\]

The only nonzero rows of H_K are

\[
 (H_K)_0=2(p,q),\quad (H_K)_1=-(e_0+2\alpha)W,\quad
 (H_K)_2=-3e_0W,\quad (H_K)_4=(H_F)_1Q-W_1.
\]

Define the six rows of T as follows. First set

\[
 T_0=e_2,\qquad T_3=e_5+L_3,\qquad T_5=Z_4+L_5.
\]

For r=1,2, let t_1=o and t_2=3o/2. Set T_{r,2}=t_r, T_{r,3}=T_{r,5}=0, and set its columns I to

\[
 T_{r,I}=\bigl((H_F)_rC-V_r-t_r(H_F)_2\bigr)(H_F[I,:])^{-1}.
\]

Finally set

\[
 T_4=\frac{e_3-e_2+\alpha L+pT_3+qT_5-pT_1}{q}.
\]

This defines every entry of B,Z,T as a rational function of the seven parameters.

## 3. The normalized terminal column

The following small linear system is a compact alternative to the fully expanded formulas for v. Put

\[
 M=I_6-VE,\quad R_Z=Z[I,:]-PE,\quad R_B=B[I,:],\quad R_T=R_B-PE.
\]

Define a 6-by-6 matrix U by

\[
\begin{aligned}
 U_1&=-2e_0+2\alpha VE,& U_2&=0,& U_3&=-2\alpha M,\\
 U_4&=(H_F)_1R_Z+(H_K)_1\Delta,&
 U_5&=(H_F)_1R_Z,\\
 U_0&=\bigl((H_F)_4R_Z+(H_K)_4\Delta-hU_1-iU_4\bigr)/g.
\end{aligned}
\]

Form three explicit 6-by-6 matrices

\[
\begin{aligned}
 D_B&=BU-H_FR_Z-H_JR_B-H_K\Delta+M,\\
 D_Z&=ZU-H_FR_Z-H_JZ[I,:]+M,\\
 D_T&=TU-H_JR_T+M.
\end{aligned}
\]

Set v_0=1 and determine its other five coordinates by

\[
 (D_Bv)_2=(D_Bv)_3=(D_Bv)_5=(D_Zv)_4=(D_Tv)_1=0.       \tag{3}
\]

In row order as written and unknown-column order (v_2,v_3,v_5,v_4,v_1), the coefficient determinant at x=0 is 4. Thus (3) defines v uniquely by an ordinary 5-by-5 unit matrix inverse. In particular,

\[
 v(0)=(1,3,3,3,12,12)^\mathsf{tr}.
\]

Now define K by the following six explicit rows:

\[
\begin{aligned}
 gK_0&=3he_0+2ie_1-2e_4-e_3B-2\alpha ZB+2i\alpha B,\\
 K_1&=K_2=-3e_0,\\
 K_3&=-e_0-2\alpha,\\
 K_4&=-2e_1-2\alpha B,\\
 K_5&=-e_1-e_3-2\alpha Z.
\end{aligned}
\]

Equations (1), (2), and the rational definitions above are the promised explicit finite system.

## 4. Why a formal branch exists

An exact rational calculation supplies a degree-eight center jet y_* with the displayed degree-four prefix. Substitution gives F(y_*)=0 modulo x^9. The Jacobian at that jet has invariant-factor valuations

\[
 0,0,0,0,0,4,4,
\]

and corresponding nonzero leading pivots

\[
 -1/24,\quad54,\quad9/2,\quad-81,\quad2,\quad24,\quad-8/3.
\]

Therefore its inverse has pole order at most four. Singular Hensel/Newton lifting gives a unique formal solution congruent to y_* modulo x^5. Rational denominators are units: q(0)=1/18, s(0)=9/2, g(0)=12, det C(0)=12, det H_F[I,:](0)=-1/3, and the determinant in (3) is 4. The complete seed and exact replay are in the certificate packet. This establishes existence, not merely consistency of finitely many fitted coefficients.

## 5. Why this branch counts the full class

The exact lazy normal form counts distinct permutations by unique output codes. Two counting reductions replace a valid Z O^a run by Z^(a+1), and replace a positive-prefix clause C_m by the signed word polynomial B^m-(B-Z)^m. Consequently all unrestricted completion counts satisfy an exact signed three-letter recurrence.

Its held-deletion suffix operators have a four-channel finite transducer. The corresponding all-word residual has an exact 19-to-9 suffix quotient. The matrices above give an invariant six-row graph [I_6,H], where

\[
 H=[H_F,H_J,H_K,U\beta],\qquad \beta=\frac{2v}{1-xv_2}.
\]

All graph transition and initial-row identities are rational identities. The five equations (3) force every remaining E-column identity after the substitution T_{2,2}=3T_{1,2}/2. The first equation of (1) makes the graph annihilate the terminal column. Its second equation gives the second empty-word boundary. The normalization in (2) supplies both root and height-one exceptions.

Thus every word residual vanishes, including arbitrarily long words and arbitrary future record jumps. Every recurrence summand reduces “future input count + held height” by one. Induction on this integer gives coefficientwise uniqueness of the infinite recurrence. The finite branch therefore represents the actual full permutation-count generating function.

No finite-capacity cutoff, bounded held rank, subclass intersection, state-inventory generating function, or polynomial interpolation is involved in the identification.

## 6. Reproducible certificate dependencies

- `eight-parameter-matrix-closure.json`: explicit rational matrix family.
- `verify_eight_parameter_invariant.py`: exact non-E transition/initial identities.
- `eight_parameter_beta_elimination.json`: expanded normalized direction and unique remaining E factor.
- `verify_seven_parameter_epsilon.py`: separate reconstruction of E identities and compact K.
- `seven_parameter_full_system_certificate.json`: exact degree-eight seed and Jacobian pivots.
- `certify_seven_parameter_full_system.py`: exact rational Hensel replay.
- `full_seven_parameter_polynomial_system.json`: expanded finite polynomial arithmetic-circuit export.
- `signed-three-letter-system.md`, `signed-suffix-transducer.md`, `compressed-residual-automaton.md`, `conditional-fifteen-state-quotient.md`: exact combinatorial and residual transformations.
- `finite-certificate-identification.md`, `reduced-root-normalization.md`: all-word counting uniqueness and boundary identification.

