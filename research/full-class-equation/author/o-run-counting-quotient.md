# An exact O-run quotient for unrestricted completion counts

This is a counting simplification for the full unrestricted (3,3) class, not an explicit algebraic equation, finite-interface theorem, or labelled-language quotient. No historical-priority or formal-certification claim is made.

## 1. Objects

Use the maximum-insertion coordinate normal form. A state S is a Cartesian product of factors Z={0}, O={1}, B={0,1}, T={0,1,2}, and C_m={0,1}^m minus {1^m}. A coordinate j inserts label j at the indicated zero-based physical slot. The represented set of physical stacks is denoted L(S).

For h=height(S), let c(S,m) count distinct output permutations on the old labels 1,...,h and exactly m new input labels h+1,...,h+m, starting from some stack in L(S), with all tokens eventually output. Physical histories do not receive multiplicity. The next input labels arrive in increasing order, and insertion/removal slots are 0,1,2 without a capacity bound. Put C_S(x)=sum_{m>=0} c(S,m)x^m. In particular C_empty(x) is the requested full permutation OGF, including the empty permutation once.

For every reachable normal-form word, each O is immediately preceded by Z or O. This is the separate reachable-factor-language invariant. Define q(S) by replacing every O factor with Z, leaving all other factors (including clause lengths) unchanged.

**Theorem.** For every reachable S, and every m>=0, c(S,m)=c(q(S),m). More generally this equality holds for every valid coordinate state in which every O belongs to a block Z O^a of consecutive unary factors. A fixed permutation of the old labels maps L(S) bijectively onto L(q(S)).

## 2. One fixed run

Consider S=P Z O^a W, where the displayed block uses consecutive labels l,l+1,...,l+a. Every stack represented by P consists of smaller labels. Applying Z inserts l on top. Then each O inserts the next label immediately below that same top label l. Hence after this block the physical stack is

    (l, l+a, l+a-1, ..., l+1, old_stack).

Replacing the block by Z^(a+1) gives

    (l+a, l+a-1, ..., l, old_stack).

Let rho fix labels outside this block, and set

    rho(l)=l+a,
    rho(l+j)=l+j-1 for 1<=j<=a.

This fixed cyclic relabelling maps the first displayed stack to the second for every choice of old_stack. It does not depend on that choice.

Every coordinate in W introduces a label greater than all labels in the block. Applying rho to the existing stack commutes with inserting that new label at its chosen slot. The allowed digit words of W, including correlations within each C_m, are identical in the two states. Therefore rho maps the entire L(P Z O^a W) bijectively onto L(P Z^(a+1) W).

Different maximal O-runs use disjoint label blocks. Apply the corresponding relabellings successively (equivalently, compose their disjoint permutations). This maps L(S) onto L(q(S)). The argument uses factor boundaries: an arbitrary forced O after B, T, or C_m is not covered.

## 3. Relabelling continuations

The composed rho fixes every future label h+1,h+2,... . Apply rho to each old token in a physical history, and leave each insertion/removal slot and the order of newly consumed inputs unchanged. Every operation is legal in exactly the same cases, because legality depends only on physical position. This gives an invertible map between complete histories starting in the two initial stack sets.

More importantly, the map acts on the output permutation itself by the same fixed relabelling. Thus it induces a bijection of *distinct admitted outputs*: an output is feasible from some initial stack on one side if and only if its relabelled output is feasible on the other. No choices of realizing history or initial physical order are counted. The number m of new labels is preserved. This proves the theorem for all m.

The two states need not have equal labelled continuation languages. For example ZO and ZZ are different singleton physical orders; the prior top-query gadget distinguishes them. Their univariate completion counts agree by this relabelling.

## 4. Exact quotient recurrence

Let d(S,k) be the exact normal-form state after outputting held rank k; omit terms where it rejects. Let r(S,b) append b-1 held inputs and immediately output the bth new input, as in lazy record N_b. Then

    c(S,m) = [S=empty and m=0]
             + sum_{b=1}^m c(r(S,b),m-b)
             + sum_{k=1}^{height(S)} c(d(S,k),m).

This is the exact unique-output-code completion recurrence. Its induction measure is m+height(S): a record term has measure one smaller, as does a held-output term. Thus it determines every finite c(S,m) uniquely.

For O-free reachable representatives Q, replace each target above by q(target). Section 3 proves the equality of the individual target counts. The resulting quotient recurrence therefore computes exactly the same full unrestricted completion numbers, including c(empty,m). Different ranks k remain separate summands even if they lead to the same normalized target. The same is true of distinct record letters.

This is a weighted enumeration quotient, not an assertion that the original labelled output codes have the same transition targets after O erasure. A decoder would have to carry the induced old-label relabellings. It also does not justify replacing the ordered B/T word by counts, or erasing the C_m exclusion.

The quotient still has infinitely many states and can rewrite an arbitrarily long suffix. The theorem removes O-runs as independent data for univariate enumeration. It does not supply a finite polynomial system by itself.

## 5. Countercontrol and finite corroboration

The condition on O-runs is essential. The valid but unreachable factor state ZBO does not satisfy it. Its completion coefficients through m=6 are

    6,24,120,708,4740,35016,279036,

whereas ZBZ gives

    6,24,120,708,4692,33936,263292.

Thus blindly replacing every O in every syntactically valid state is false; the first discrepancy here is at four new input tokens.

The accompanying standard-library checker constructs physical stack sets independently from factor digit choices and tests the explicit relabelling on all 3,197 reachable-syntax states through height seven, covering 74,231 represented orders. It also checks 1,150 completion-count comparisons for initial height at most five and m<=4 using the reviewed normal-form recurrence. These are finite corroboration, not the all-length proof.

Dependencies: the reviewed exact decorated-factor normal form and unique lazy codes; the reachable O-predecessor invariant, proved in research/reachable-factor-language/reachable-factor-language.md. Source baseline is commit aedaeef7e9f8c3f8aa3011ed5044dee64d09a540. The literal relabelling proof itself only needs the stated coordinate-factor interpretation and O-run hypothesis.
