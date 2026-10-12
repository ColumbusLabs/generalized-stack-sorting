# Exact root and preload boundary identities

Derivation, 10 October 2026. This follows directly from the reviewed unrestricted lazy recurrence; it needs no six-mode assumption.

Let

    g=Phi(empty), d=Phi(Z), h=Phi(ZB), q=Phi(ZBT),
    A=sum_{j>=0} x^j Phi(ZB T^j).

All series count distinct completions, with x marking new input tokens and initially held labels unweighted. First-output decomposition gives

    g=1+xg+x^2 d+x^3 A,
    d=g+xd+x^2 A,
    h=2d+xA.

The first two equations imply g=1+xd. Combining with the third yields d=1+xh. Consequently

    G(3,3)=g=1+x+x^2 Phi(ZB).

For ZBT each of its three held-rank outputs has successor ZB. Its record term is A-h, hence

    q=3h+(A-h)=A+2h.

Substitution into h=2d+xA and d=1+xh gives h=2+xq. Therefore also

    G(3,3)=1+x+2x^2+x^3 Phi(ZBT).

These identities express exact preloading for two and three old tokens, as a consequence of unique lazy codes. They do not assume that an arbitrary supplied initial stack order has the same continuation language.

In the exploratory six-row gauge epsilon,B,T,Z,BB,BZ for H(w)=Phi(ZB w), the terminal column beta has h=beta_0 and q=beta_2. Thus a prospective matrix certificate must satisfy

    beta_0=2+x beta_2,
    G(3,3)=1+x+x^2 beta_0.

No finite matrix realization is asserted by these identities.
