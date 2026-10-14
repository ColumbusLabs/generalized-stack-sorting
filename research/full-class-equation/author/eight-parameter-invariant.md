# Exact eight-parameter non-E invariant family

Scope of this supplement: this is an intermediate derivation retained to explain the construction. Its conditional statements are local to this note. The completed actual-count and exact-degree certificates are documented in [the current formal scope](../../../formal/CLAIMS.md); the hypotheses below are not unresolved premises of those final theorems.

Derived 10 October 2026. This is a rational parametrization satisfying every non-E transition and initial-row condition of the 15-state graph certificate. It is independent of any coefficient fit once the formulas are stated: the accompanying exact verifier checks 203 scalar rational identities. The E-column, scalar boundary equations and existence of a formal parameter branch still remain to be supplied.

## Parameters and branch point

Take free parameters (g,i,p,q,s,c,o,w), with initial values

    (12,8,-4/9,1/18,9/2,2,6,9).

Set

    h=(2 i p q s+i q+2 p^2 s+p-2 q s)/(2 q^2 s),
    v0=1+q(h-pg),  v1=p+q(i-qg),
    d=-1/(2q)-s(p/q+qg),
    j=g-(s+pd)/q,
    e=pd-s v0,  f=qd+1/2-s v1,
    k=h-pg+pj-(p/q)(e-pd)+1/(2q),
    l=i-qg+qj-(p/q)(f-qd)+p/q,
    a=(c-3/2+3s v1)/q,  b=pa-3s v0.

Here a,b,d,e,f,h,j,k,l are auxiliary scalar names, not the boundary row denoted alpha below. Let

    A=[[0,1,0],[0,0,1],[a,b,c],[d,e,f],[g,h,i],[j,k,l]].

For the six coordinate rows e0,...,e5, define

    E=[e0;e1;e4],
    alpha=e0+p(e1-e3)+q(e4-e5),
    R=[alpha;e3;e5], B=A E, Z=A R.

These formulas give B and Z, with the required fixed row gauge and shared left kernel. Their only scalar denominators are powers of q,s and rational constants.

## Constructing T without large expanded expressions

Construct C,V,W,P,Q,D and H_F,H_J,H_K as in `explicit-nonepsilon-graph-blocks.md`. Let J=H_F[(0,1,4),:]. Its determinant at the displayed point is -1/3, so it is a unit in the selected formal neighborhood.

Set T_0=e2, T_3=e5+(B-Z)_3, T_5=Z_4+(B-Z)_5. For row r=1 or2 choose t_1=o, t_2=w. The three entries of T_r in columns0,1,4 are

    ((H_F)_r C - V_r - t_r (H_F)_2) J^(-1).

Set T_(r,2)=t_r and T_(r,3)=T_(r,5)=0. Finally set

    T_4=[e3-e2+alpha(B-Z)+p T_3+q T_5-p T_1]/q.

This last row automatically has zero entries in columns3,5. `eight-parameter-matrix-closure.json` gives every entry of A and T as expanded rational expressions; after simplification, T also has denominators only q,s and rational constants. The construction satisfies

    ZT=BZ+ZB-ZZ.

## Exact identities

For the resulting tuple, all nine block transition equations

    B H_F=H_F P-V, Z H_F=-V, T H_F=H_F C-V;
    B H_J=0, Z H_J=H_F P, T H_J=H_J P;
    B H_K=H_F Q-W, Z H_K=0, T H_K=H_F Q+H_K D-W

hold as rational identities in the eight independent parameters. The three Z-boundary containment equations from the graph note also hold identically. No truncation, finite-field specialization, or coefficient interpolation is used to verify these assertions.

A short derivational route first imposes H_F Q=-W, which has seven independent low-degree conditions. They give the displayed formulas in parameters (g,h,i,p,q,s,c). Every remaining B/Z graph-closure numerator is divisible by

    2s(p^2+i p q-h q^2-q)+(p+i q).

Its coefficient of h is -2q^2 s, a unit at the branch point. Solving it gives the stated h. The T construction then solves the remaining transition equations exactly while retaining o,w as its two free parameters.

## Reproducible finite certificate

- `eight-parameter-matrix-closure.json`: explicit A,T data; SHA256 bb27760188dd1568129a7eb77d835cbd51863f1bf600134a85262c3673255f81.
- `verify_eight_parameter_invariant.py`: a separate exact SymPy replay, reading only that matrix data and rebuilding the graph formulas.
- `eight-parameter-invariant-verification.json`: 203 zero identities PASS, unit values q=1/18, s=9/2, g=12, det C=12, det D=3, det J=-1/3.

The remaining scalar/E system must have an actual formal power-series branch through this point and satisfy every remaining graph/boundary equation. Once that is proved, the exact signed recurrence and its coefficientwise uniqueness identify the resulting root with the unrestricted class. This note does not yet claim that final identification.
