# Optional irreducibility supplement



## 5. A separate small irreducibility certificate

At x=3, reduction modulo17 gives the degree12 polynomial whose coefficients in ascending y powers are

    5,14,9,10,4,3,14,7,14,3,14,7,5.

The exact certificate `G_polynomial_irreducibility_certificate.json` verifies

    y^(17^12)=y modulo f,
    gcd(f,y^(17^6)-y)=gcd(f,y^(17^4)-y)=1,

and supplies explicit Bézout witnesses for both gcds. Rabin's criterion proves f irreducible over F17. The leading y coefficient of Q is972x⁴, nonzero at x=3 modulo17, so positive y-degrees cannot disappear under this specialization. A factor depending only on x is excluded because the leading y coefficient and constant y coefficient -8100-11016x+80028x² have gcd1 in Q[x]. Gauss's lemma and specialization therefore prove Q irreducible over Q(x).

Together with the counting identification, this proves that the algebraic degree of the unrestricted G(3,3) is exactly12. This minimality claim uses its separate irreducibility certificate; it is not inferred from the degree of a displayed equation.

