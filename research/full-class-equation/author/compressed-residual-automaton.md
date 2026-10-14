# Compressed 25-state compatibility certificate target

Scope of this supplement: this is an intermediate derivation retained to explain the construction. Its conditional statements are local to this note. The completed actual-count and exact-degree certificates are documented in [the current formal scope](../../../formal/CLAIMS.md); the hypotheses below are not unresolved premises of those final theorems.

Derivation, 10 October 2026. This is an exact reformulation of the all-word recurrence, not a certificate that the selected algebraic branch satisfies it.

Let d=6, alpha=alpha_b=e0, a=alpha_z, beta the terminal column, and R=(I-xT)^(-1). Write L=B-Z, kappa=beta-xR beta, and d0=Phi(Z). All matrices use row-vector actions. The notation d denotes matrix dimension and d0 denotes a scalar series.

## Compressed suffix automaton

The four suffix channels (F,J,K,E) have dimension 3d+1 rather than 4d, because E(w)beta is a scalar empty-word indicator multiplied by the fixed column beta. Use block order (F,J,K,E), block sizes (d,d,d,1), and terminal

    nu=(beta,beta,0,1)^tr.

Set

    N_z = [[0,Z,0,0], [0,0,0,Z beta], [0,0,0,0], [0,0,0,0]],
    N_b = [[Z,0,Z,0], [0,0,0,B beta], [0,0,0,L beta], [0,0,0,0]],
    N_t = [[B,0,Z,0], [0,Z,0,L beta], [0,0,L,0], [0,0,0,0]].

Let C_z=[I,0,0,0], C_b=C_t=[I,0,I,0]. Define a common (4d+1)-state automaton

    Q_s = [[M_s,-C_s], [0,N_s]],
    tau=(kappa,nu)^tr.

Its prefix block represents H minus record contribution and its upper-right block subtracts every internal held-deletion summand.

## Boundary derivatives

Three transient boundary channels represent Phi(zF(w)), Phi(zJ(w)), Phi(zK(w)); their empty-word values are d0,d0,0. After reading one letter their rows lie entirely in the common suffix automaton. The rows, in (F,J,K,E) order, are

    pF_z=(0,a,0,0),
    pF_b=(a,0,a,0),
    pF_t=(alpha,0,a,0),

    pJ_z=(0,0,0,a beta),
    pJ_b=(0,0,0,alpha beta),
    pJ_t=(0,a,0,(alpha-a) beta),

    pK_z=0,
    pK_b=(0,0,0,(alpha-a) beta),
    pK_t=(0,0,alpha-a,0).

Consequently the full residual has a 4d+4=28-state representation, or equivalently two empty-word scalar conditions and six initial rows in dimension 4d+1=25:

    e_b=alpha kappa-2d0=0,
    e_z=a kappa-2d0=0,

    r_b,s=(alpha M_s, -alpha C_s-2pF_s-2pK_s),
    r_z,s=(a M_s, -a C_s-pF_s-pJ_s),
    s in {z,b,t}.

All-word compatibility is exactly

    e_b=e_z=0 and r_A,s Q_w tau=0
    for A in {b,z}, s in {z,b,t}, every word w.

This supplies a substantially smaller invariant-row-module target. A certificate can provide a finite spanning family of rows containing these six initial rows, prove closure under the three Q_s, and prove annihilation by tau, using identities valid on the selected branch.

## Important structural guard

A six-dimensional kernel graph of the form {(v,vX):v in K^6} cannot work for the observed tuple. Such a graph would imply Z X_F=-I from Q_z invariance, but the candidate Z has an identically zero T-basis column and is singular. Additional vertical kernel rows in the suffix block are necessary. This does not rule out a larger finite invariant module.
