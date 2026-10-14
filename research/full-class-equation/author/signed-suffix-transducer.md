# Four-channel signed suffix transducer and finite-certificate target

Scope of this supplement: this is an intermediate derivation retained to explain the construction. Its conditional statements are local to this note. The completed actual-count and exact-degree certificates are documented in [the current formal scope](../../../formal/CLAIMS.md); the hypotheses below are not unresolved premises of those final theorems.

Derivation, 10 October 2026. This supplements `signed-three-letter-system.md`. The formulas here are an algebraic restatement, with bounded replay supplied separately. No finite-rank theorem or formal solution of a finite matrix system is asserted.

## Exact four-channel form

All multiplication below is concatenation in the free noncommutative polynomial algebra on z,b,t. Put l=b-z. Let E be the empty-word indicator: E(empty)=1 and E(a v)=0. Set

    F(empty)=J(empty)=1, K(empty)=0;
    F(zv)=z J(v);
    F(bv)=z F(v)+z K(v);
    F(tv)=b F(v)+z K(v);
    J(zv)=z E(v);
    J(bv)=b E(v);
    J(tv)=z J(v)+l E(v);
    K(zv)=0;
    K(bv)=l E(v);
    K(tv)=l K(v).

Then U=F+K gives precisely the two suffix maps in the previous note. Indeed K(t^q b)=l^(q+1) and K vanishes on all other words. J is the old F_1 map on exceptional suffixes, with its O-run replaced by Z; this replacement is used only after an immediately preceding z. The identity F(tv)=b F(v)+z K(v) in the exceptional b case follows from b-l=z. The other cases are direct.

## Matrix evaluation

Fix an arbitrary dimension d, matrices Z,B,T and a terminal column beta. Let L=B-Z. The vector of evaluated channels is

    V(v)=(F(v) beta, J(v) beta, K(v) beta, E(v) beta)^tr,
    V(empty)=(beta,beta,0,beta)^tr.

It satisfies V(a v)=N_a V(v), with 4 by 4 block matrices, each block of size d:

    N_z = [[0,Z,0,0], [0,0,0,Z], [0,0,0,0], [0,0,0,0]],
    N_b = [[Z,0,Z,0], [0,0,0,B], [0,0,0,L], [0,0,0,0]],
    N_t = [[B,0,Z,0], [0,Z,0,L], [0,0,L,0], [0,0,0,0]].

Let C_z=[I,0,0,0] and C_b=C_t=[I,0,I,0]. The summed internal held deletion of an input word w is represented in dimension 5d by

    Q_a = [[M_a,C_a], [0,N_a]],

with initial row (alpha,0) and terminal column (0,beta,beta,0,beta)^tr. The upper-right block chooses exactly one deleted coordinate; every choice remains a separate summand, including equal successor words.

## Two boundary families and exact recurrence

Write H_b(w)=Phi(zb w), H_z(w)=Phi(zz w), d0=Phi(z), and g=Phi(empty). A proposed matrix representation has H_a(w)=alpha_a M_w beta for a=b,z. Put R=(I-xT)^(-1). The exact unrestricted recurrence would require, for every w,

    H_b(w) = x alpha_b M_w R beta
               + 2 Phi(z U(w)) + internal_delete_b(w),
    H_z(w) = x alpha_z M_w R beta
               + Phi(z J(w))+Phi(z F(w)) + internal_delete_z(w).

Here internal_delete_a uses Q with initial alpha_a. The boundary terms follow by deleting one of the first two held coordinates: for zb, both yield z U(w); for zz, they yield z J(w) and z F(w).

The remaining height-zero/one equations are

    g = 1+x d0,
    d0 = g+x d0+x^2 alpha_b R beta.

For evaluating Phi(z v) in the boundary terms, extend the matrices to dimension d+1. The extra starting row has terminal value d0 and its z,b transitions go to alpha_z,alpha_b respectively. Its t transition may be zero because the images F,U,J start only with z or b when nonempty. All ordinary states use M_a. Thus the boundary terms also have explicit finite weighted-automaton representations, of dimension 4(d+1).

## What a matrix certificate must prove

For a concrete tuple of formal matrices, both residuals above are recognizable noncommutative series. Each has a direct-sum representation of dimension at most

    d + 5d + 4(d+1) = 10d+4.

The first summand represents H_a minus its record contribution. Over a field, equality to zero can be checked by finite invariant-subspace saturation, or by all words of length less than the representation dimension. A polynomial certificate may instead supply an invariant subspace containing the initial row and annihilating the terminal column. Resolvents can be introduced with polynomial equations (I-xT)R=I.

For the observed d=6 ansatz, this gives residual automata of dimension at most 64. It is a concrete finite verification target, not a proof that suitable matrices exist. In particular, a finite polynomial constraint system obtained from these identities could be inconsistent as formal series, or have an unwanted branch. A publishable explicit equation still needs an actual selected formal solution, an all-word certificate, and the boundary conditions above. The retained coefficient fits establish none of those existence obligations.
