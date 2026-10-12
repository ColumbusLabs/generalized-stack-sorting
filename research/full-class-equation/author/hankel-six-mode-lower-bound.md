# Exact six-mode lower bound for the three-letter completion series

Derivation and exact finite certificate, 10 October 2026. This is a lower bound on linear state representations of the auxiliary word series; it is neither an upper bound nor a lower bound on the algebraic degree of G(3,3).

Let H(w)=Phi(ZB w), where Phi counts all unrestricted completions with new input marked by x. Form the Hankel submatrix H_uv=H(uv), using ordered row words

    empty, B, T, Z, BB, BZ

and ordered column words

    empty, B, BB, TB, BZ, T.

The exact completion coefficients give

    det(H_uv) = -71663616 x^8 + O(x^9).

Therefore this minor is nonzero over Q((x)). If H(w)=alpha M_w beta in dimension d over any field extension of Q((x)), its Hankel matrix factors as rows alpha M_u times columns M_v beta, and hence has rank at most d. The displayed nonzero minor proves d>=6.

Only finitely many exact coefficients are needed for this lower bound. Their validity comes from the exact unrestricted completion DP, not from interpolation of a prospective equation. The original 40-by-40 packet was independently checked in all 14,400 entries through degree eight; the later six-by-six degree16 packet was computed by the independent compact completion counter. The determinant and candidate matrix reconstructions are in `six-transfer-candidate-degree8.json`, based on the data packet `six-boundary-matrices-degree16.json` in the coefficient worker's directory.

The same packet yields determinant coefficients at degrees nine and ten of -5088116736 and -196525522944. These are redundant checks; the nonzero degree-eight coefficient already proves the bound. No assertion that all larger Hankel minors vanish is made.
