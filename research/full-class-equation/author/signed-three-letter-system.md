# Exact signed three-letter completion system

They give an exact word-indexed recurrence, not a finite polynomial system.

## 1. Linear notation

Let z,b,t be noncommuting letters denoting Z,B,T. For a finite signed sum of state words, extend the completion functional Phi linearly. All representatives have first letter z, and their second letter is not t. Use lambda=b-z and the morphism phi(b)=z, phi(t)=b.

The normal form and new counting reductions eliminate every O by its Z-run relabelling and every clause by

    C_m = b^m - lambda^m

inside the completion functional. Distinct held-output ranks remain distinct summands. No subtraction of physical histories is performed.

## 2. Two exact suffix operators

Define U(empty)=F(empty)=empty_word. On an exceptional nonempty suffix t^q a, q>=0, a in {z,b,t}, set

    U(t^q z)=b^q z,
    U(t^q b)=U(t^(q+1))=b^(q+1),

    F(t^q z)=b^q z,
    F(t^q b)=b^(q+1)-lambda^(q+1),
    F(t^(q+1))=b^(q+1).

If a word W is not exceptional, write it uniquely as v a E, where E is its longest exceptional suffix, a is b or z, and v is the preceding word. If v contains z, set F(W)=U(W)=0. Otherwise v is in {b,t}* and

    F(v b t^q z)=phi(v) z b^q z,
    F(v b t^q b)=F(v b t^(q+1))=phi(v) z b^(q+1),

    F(v z t^q z)=phi(v) z^(q+2),
    F(v z t^q b)=F(v z t^(q+1))=phi(v) z^(q+1) b.

For every nonexceptional word, U(W)=F(W).

These formulas follow directly from the reviewed F_0,F_1,U identities. The only clause-producing case on an O-free, clause-free input is F(t^q b); it has been replaced by the proved valuation polynomial. In the Z branch, the forced O^q run is preceded by Z, which is exactly the hypothesis needed for its counting relabelling.

## 3. Held deletion and records

For a selected letter a in state p a w:

    a=z:  replace p a w by p F(w),
    a=b or t: replace p a w by p U(w).

All terms are interpreted linearly after expansion, with zero discarded. The selected coordinate is removed, so every surviving word has one fewer held token.

Let append(S,j) add j new held labels: it appends z at height zero, b at height one, and t at larger heights. A lazy record consuming j+1 new inputs and outputting its final one has weight x^(j+1) and target append(S,j). For states of height at least two, this is S t^j.

## 4. Exact recurrence and selected solution

Writing c(S,n) for n further input tokens, extend c linearly to signed word sums and use

    c(S,n) = [S=empty and n=0]
             + sum_{j=0}^{n-1} c(append(S,j),n-j-1)
             + sum_{selected coordinates i} c(delete_i(S),n).

Every recursive call decreases n+height(S) by one. Therefore the recurrence has a unique coefficientwise finite solution. Its root c(empty,n) counts the full unrestricted permutation class, by the reviewed normal-form recurrence and the two counting reductions.

For nonempty height-at-least-two states this is equivalently

    Phi(S) = x sum_{j>=0} x^j Phi(S t^j)
             + sum_i Phi(delete_i(S)).

The complete root also has the empty output contribution and the height-zero/one append exceptions. An ordinary finite-capacity cutoff or a bounded held-rank cutoff is not imposed.

## 5. Precise remaining equation-extraction problem

The deletion map is now a finite signed rational transduction over a three-letter alphabet: the exceptional tails, morphism phi, and two terminal cases are all finite-state. Nevertheless it rewrites arbitrarily long suffixes. A rational stack transducer is not automatically an ordinary PDA, and this word-indexed recurrence is still infinite.

A finite-rank matrix ansatz Phi(zb w)=alpha M_w beta has survived the retained bounded tests with six modes. The selected six-by-six Hankel minor is nonzero, so fewer than six modes cannot handle the tested BTZ context family. The matrix ansatz has no proved upper bound. To obtain the requested equation one must either:

1. prove a finite first-return/interface decomposition for the signed transduction; or
2. exhibit a finite matrix polynomial system, prove existence of its selected formal branch, and verify the recurrence as a rational-series identity for every valid word.

Checking many coefficients, finding low-rank truncations, or merely writing an overdetermined matrix ansatz does not establish either obligation.
