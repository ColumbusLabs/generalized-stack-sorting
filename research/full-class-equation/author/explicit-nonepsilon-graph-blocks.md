# Explicit nonempty-channel graph blocks in the conditional 15-state quotient

Derivation, 10 October 2026. These are candidate graph formulas forced by the B-family initial rows and graph closure, under the matrix-shape ansatz. They are not asserted to satisfy every closure identity yet. This gives finite rational data to test, with unit denominators.

Use I=(0,1,4), C=B[I,I], V=B[:,I]C^(-1), W=(B-Z)[:,(1,4)], and let a=alpha_z=e0+p(e1-e3)+q(e4-e5). Put

    P=Z[I,:] V, Q=Z[I,:] W,
    D=[e1-e3; e4-e5] W.

Let f0=(1,0,0), f1=(0,1,0), and u=-2 f0 C^(-1). The first eight suffix coordinates of the six-row graph H split as H_F (6 by3), H_J (6 by3), H_K (6 by2). Candidate explicit rows are

    H_F = [u;
           uP-f0;
           -3f0;
           -f0;
           (uP-f0)P-f1;
           -f1],

    (H_J)_3=-2 aV,
    (H_J)_5=-e3 V-2 a Z V,
    every other row of H_J is zero,

    (H_K)_0=2(p,q),
    (H_K)_1=-(e0+2a)W,
    (H_K)_2=-3 e0 W,
    (H_K)_4=(H_F)_1 Q-W_1,
    (H_K)_3=(H_K)_5=0.

The H_F row zero follows from the T derivative and T_0=e2: uC=-2f0. The H_K row zero follows from the same derivative and the invertibility of D: H_K,0 D=2(p,q)D. D has determinant3 at the retained constant tuple, so this is a unit condition. All remaining displayed rows come directly from the B-family words B,T,Z,BB,BZ.

The non-E transition closure conditions are exactly

    B H_F=H_F P-V,  Z H_F=-V,  T H_F=H_F C-V;
    B H_J=0,       Z H_J=H_F P, T H_J=H_J P;
    B H_K=H_F Q-W, Z H_K=0,    T H_K=H_F Q+H_K D-W.

The three Z-boundary first-letter containment conditions reduce, using these transition equations, to

    a H_F=-f0 C^(-1),
    a H_J P=-aV,
    a H_K=0.

The E-column graph coordinate and terminal/empty-word conditions are separate and depend linearly on beta once the matrices are fixed.

`probe_symbolic_graph_shapes.py` substitutes the 22-parameter matrix ansatz into these formulas, cancels unit denominators, and emits exact integer polynomials in `symbolic-graph-shape-equations.json`. It currently retains 82 distinct numerator polynomials; many are algebraically dependent. Their vanishing on the selected branch still needs proof. The denominators are powers of the explicit unit parameters g=B_(4,0) and q (constant terms12 and1/18), plus the already stated determinant unit if deriving rather than postulating H_K,0.
