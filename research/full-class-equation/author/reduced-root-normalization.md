# Scalar normalization for a completed graph certificate

Exact derivation, 10 October 2026. Assume the matrix graph certificate's E-column has been supplied as H_E=U beta, and put K=(H_F+H_J)E+U, so the terminal condition is

    (I+K) beta = x r,  r=(I-xT)^(-1) beta.

For the present gauge K_1=K_2=-3e0 and T_0=e2. Assume beta0 has constant term2, hence is a unit. Set v=beta/beta0, t=v2; then v0=1 and t(0)=3.

All scalar normalization can be expressed as

    beta0=2/(1-x t),
    G=1+x+2x^2/(1-x t).

Indeed the exact root/preload identities give beta0=2+x beta2. Alternatively the terminal row2 and resolvent row0 imply r0=beta2-2beta0 once empty_B and the height-one boundary are imposed.

For constructing a new formal branch, one may instead impose

    [(I-xT)(I+K)-xI] v=0,
    (alpha-e0) K v=0,

together with v0=1,v2=t and the E/initial graph constraints. Define beta0, beta=beta0 v, r=(I-xT)^(-1)beta, and d0=1+x beta0 by the displayed rational normalization. Then the six terminal equations hold by construction. Their rowzero, using T_0=e2 and K_2=-3e0, gives

    1+K_0 v=x(t-2),
    r0=beta0(t-2).

It follows that beta0-xr0=2d0 because beta0(1-xt)=2. The second displayed scalar equation makes alpha(beta-xr)=e0(beta-xr), giving the other empty-word condition. Finally the height-one relation d0=g+x d0+x^2 r0 holds with g=1+x d0 by direct substitution. Thus no additional root/height-one equation is lost.

After a proved E-column elimination, these equations may reduce to six terminal equations and one empty-Z equation in a small scalar parameter family. This note does not assert that an E elimination or a regular formal parameter branch has already been established.
