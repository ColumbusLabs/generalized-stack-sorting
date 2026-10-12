# The explicit unrestricted G(3,3) equation

This equation is for the full permutation-count ordinary generating function, including the empty permutation.

## The equation

Write

\[
Q(x,y)=A_0(y)+xA_1(y)+x^2A_2(y)+x^3A_3(y)+x^4A_4(y)+x^5A_5(y)+x^6A_6(y),
\]

where

\[
\begin{aligned}
A_0={}&-(y-1)^4(11y-18)(71y^3-414y^2+783y-450),\\[2pt]
A_1={}&-2(y-1)^3(744y^6-6811y^5+25869y^4-48798y^3+41724y^2-7398y-5508),\\[2pt]
A_2={}&(y-1)^2(5103y^8-40638y^7+119399y^6-150604y^5+94714y^4\\
&\hspace{39mm}-174168y^3+373266y^2-307764y+80028),\\[2pt]
A_3={}&-4y(y-1)(999y^9-7497y^8+17661y^7-16536y^6+43581y^5\\
&\hspace{26mm}-155839y^4+204517y^3-60318y^2-57006y+30303),\\[2pt]
A_4={}&y^2(972y^{10}-6912y^9+8604y^8-23076y^7+251778y^6-671588y^5\\
&\hspace{20mm}+524094y^4+235008y^3-434593y^2+67968y+47583),\\[2pt]
A_5={}&2y^3(972y^8+10260y^7-61902y^6+77520y^5+38718y^4\\
&\hspace{27mm}-97642y^3+4688y^2+24047y+2610),\\[2pt]
A_6={}&-y^4(6y^2-10y-5)(864y^5-1242y^4-1458y^3+1563y^2+716y-20).
\end{aligned}
\]

Then

\[
\boxed{Q\bigl(x,G(3,3;x)\bigr)=0.}
\]

The required branch is uniquely specified by

\[
\boxed{G=1+x+2x^2+6x^3+24x^4+120x^5+720x^6+5004x^7
       +38844x^8+325692x^9+O(x^{10}).}
\]

The condition G(0)=1 alone is insufficient. The polynomial has69 nonzero integer terms, degree6 in x and degree12 in y. Its exact coefficient list is `direct-G33-equation.json`.

## 1. Existence and uniqueness of this scalar branch

Let

    C8=1+x+2x²+6x³+24x⁴+120x⁵+720x⁶+5004x⁷+38844x⁸.

Exact polynomial arithmetic shows that

\[
R(x,z)=x^{-20}Q(x,C8+x^9z)
\]

is a polynomial, and

\[
R(0,z)=-16(z-325692)(z-325656),\qquad
R_z(0,325692)=-576.
\]

Thus the ordinary formal implicit-function theorem gives exactly one z in Q[[x]] with z(0)=325692 and R(x,z)=0. This proves existence and uniqueness of the displayed G branch directly; no generic MSO theorem or seven-variable singular-Hensel theorem is needed here.

For the finite rational-reconstruction check below, a displayed degree28 center is included in `scalar_G_branch_certificate.json`. Exact substitution gives Q(center)=O(x^40), with derivative leading term -576x^11. Equivalently the corresponding degree19 center for z solves R modulo x^20. The unique ordinary-IFT solution therefore agrees with that center modulo x^29 in G. This is more precision than needed to verify every exceptional denominator and the recovered coordinate jets.

## 2. Rational reconstruction into the proved finite counting certificate

Five explicit rational functions a(y,x), t(y,x), u(y,x), i(y,x), q(y,x) are supplied in `parameter_map_candidates_exact.json`. The historical filename records how they were discovered; the proof below uses exact polynomial divisibility, not interpolation.

On the selected scalar branch, their numerator and denominator valuations agree. The denominator valuations and leading coefficients are:

| coordinate | valuation | leading coefficient |
|---|---:|---:|
| a | 10 | -186624 |
| t | 12 | 2304 |
| u | 10 | -1036800 |
| i | 12 | 288 |
| q | 10 | 567787968 |

Consequently the rational functions are regular formal series. Their constants are (2,1/4,1/6,8,1/18). These nonzero leading coefficients are obtained by exact substitution into the uniquely specified scalar root, using fewer than29 coefficients. No exceptional denominator is silently treated as a unit.

Recover the original matrix parameters by

\[
g=\frac{u}{qt},\quad s=\frac tq,\quad o=i-a,\quad p=-iq,
\]

and by the explicit unit linear solution for c in `five_scalar_reduction.json`. The coefficient of c in that equation has constant6. The recovered seven-coordinate jet agrees through degree4 with the frozen finite-certificate jet; in particular its constant tuple is

\[
(g,i,p,q,s,c,o)=(12,8,-4/9,1/18,9/2,2,6).
\]

Every matrix/invariant denominator is therefore a unit, exactly as in the seven-system construction.

## 3. Exact identities, not fitted equations

The five transformed scalar equations are the following invertible triangular recombination of the six terminal equations F0,...,F5 after setting p=-iq and eliminating c by F2:

    F1-o F0,
    F3,
    F5-i F3,
    F4-(io-1/q)F0-i(F1-o F0),
    F0 after the c substitution.

Their explicit rational numerators are frozen in `changed_scalar_coordinates.json`. At the recovered constant tuple, their denominators are respectively

    -1/54, -1/27, -1/27, -1/108, 2/81.

The recombination is reversible, so vanishing of these five numerators, together with the c definition, implies all six terminal equations. The seventh, empty-boundary equation vanishes identically after p=-iq.

For each transformed polynomial, substitute the five rational functions of y,x and multiply by the product of denominator powers prescribed by its degree in each variable. The resulting polynomial in Z[x,y] is exactly divisible by Q(x,y). The replay `verify_G_polynomial_by_homogenization.py` verifies all five divisions. The largest numerator has only3051 terms and bidegree(81,43) in (y,x).

A sixth exact division verifies the output identity

\[
y=1+x+\frac{2x^2}{1-xv_2},
\]

where v2 is the normalized terminal coordinate after c recovery. Its denominator has nonzero constant -2/81 in the retained rational expression. Thus the scalar root y is exactly the output of the finite counting certificate, not merely an auxiliary series associated to it.

## 4. Identification with unrestricted permutation counts

The lazy normal form assigns one output code to each distinct output permutation. The Z O^a relabelling and exact clause valuation reduce its unrestricted completion counts to the signed three-letter recurrence. The finite residual automaton, its exact suffix quotient, and the explicit invariant graph prove every word equation for the reconstructed matrices. All held ranks retain their separate summands, and all record jumps are included.

The scalar branch just constructed supplies a regular solution of that complete finite certificate. The root and height-one identities give its output as 1+x+2x²/(1-xv2). For a completion problem with n future inputs and h held labels, every recurrence term lowers n+h by one. Induction gives coefficientwise uniqueness. Therefore the finite-certificate output, and hence the selected root of Q, is exactly the full unrestricted G(3,3).

The proof uses neither a finite-capacity cutoff nor a basis or state-inventory generating function. Discovery used coefficient reconstruction, but every all-length assertion now follows from exact rational identities, polynomial divisions, a nonsingular scalar branch, and counting uniqueness.

## Exact replay packet

- `direct-G33-equation.json`:69 integer coefficients, grouped display, and branch.
- `parameter_map_candidates_exact.json`: explicit rational reconstruction.
- `G_polynomial_homogenization_certificate.json`: six exact polynomial divisions.
- `scalar_G_branch_certificate.json`: degree28 center and denominator ledger.
- `scalar_G_ordinary_ift_certificate.json`: nonsingular scalar blowup, recovered seven-coordinate jet, and all boundary denominator constants.
- The corresponding `verify_...` and `certify_...` scripts, plus the frozen finite-counting proof dependencies.

Formalization in Lean is a separate deliverable. These are exact independently replayable algebraic and combinatorial certificates; this note does not claim that the complete theorem has already been checked by the Lean kernel.
