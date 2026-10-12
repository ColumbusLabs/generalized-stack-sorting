# The complete (3,3) basis

The global width theorem and exact finite-state construction give the following all-length classification.

## Complete structural description

Use one stack, top first, with insertion and removal at zero-based positions
0, 1, or 2 whenever valid. Let G be its outputs from increasing input.
The sortable-input basis consists of the inverses of the basis of G.

**A permutation belongs to the generated-output basis if and only if its unique
lazy code is accepted by the 28-state grammar below.** This describes ordinary
minimal forbidden permutations for the unbounded machine, not a separate
physical-capacity basis. The global proof shows every basis permutation p has

    w(p) = 1 + max_i(p_i-i) <= 7.

For a sortable-input basis permutation q the corresponding inequality is
`1 + max_i(i-q_i) <= 7`. These orientations need not be the same permutation set.

Here is the decoder. Start with no held labels and maximum read label M=0.

- N_b reads the next b increasing labels M+1,...,M+b and outputs M+b;
  the other b-1 labels remain held, and M becomes M+b.
- H_k outputs the kth smallest held label and removes it from the held set.

The code begins and ends with no held labels. Each letter outputs one value,
so accepted code length is permutation length. The encoder is unique: a new
left-to-right maximum is N_b, with b its increase over the previous maximum;
any other output is H_k, with k its rank among held labels. This code counts
permutations exactly once, independently of how many operation histories
realize their deletions.

Start in state 0; accept only in state 24. A missing transition rejects. Every
entry `N_b -> t` or `H_k -> t` means emit that code letter and move to t.
Equivalently, replace each edge q --a--> t by the grammar production q -> a t,
and add 24 -> empty. The table is a literal rendering of the independently
reviewed [DFA certificate](../evidence/three-three-bounded-basis/basis-dfa-width-7.json).

```text
 0: N5 -> 1, N6 -> 2, N7 -> 3
 1: H1 -> 4, H2 -> 4, H3 -> 4
 2: H1 -> 5, H2 -> 5, H3 -> 5
 3: H1 -> 6, H2 -> 6, H3 -> 6
 4: N2 -> 7, N3 -> 6
 5: H1 -> 8, H2 -> 8, N2 -> 6
 6: H1 -> 9, H2 -> 9
 7: H1 -> 8, H2 -> 8
 8: H2 -> 10, H3 -> 10, N2 -> 11, N3 -> 12
 9: H1 -> 13
10: N3 -> 14, N4 -> 15
11: H1 -> 13, H3 -> 16
12: H3 -> 9
13: H1 -> 17, H2 -> 17, H3 -> 17
14: H1 -> 18, H3 -> 16
15: H1 -> 19, H3 -> 9
16: H2 -> 10, N2 -> 9
17: H1 -> 20, H2 -> 20
18: H1 -> 10, H3 -> 21, N2 -> 22, N3 -> 23
19: H2 -> 13
20: H1 -> 24
21: N3 -> 25, N4 -> 26
22: H2 -> 13, H3 -> 27
23: H3 -> 19
24: 
25: H2 -> 18, H3 -> 27
26: H2 -> 19, H3 -> 19
27: H1 -> 10, N2 -> 19
```

The only cyclic strongly connected component is
`{10,14,16,18,21,22,25,27}`. Thus this is a finite regular grammar for all the
infinite obstruction families, with finite entry and exit pieces. It is a
structural description of actual permutations, not merely a recurrence for
their number.

## Exact basis enumeration

The generating function counting basis permutations by length is

    B_(3,3)(x) = 36 x^7 (1+3x+2x^2+3x^3+x^5-x^6)/(1-3x^3-x^5).

Its coefficients at lengths 7 through 16 are

    36, 108, 72, 216, 324, 288, 720, 1044, 1080, 2484.

There are none below length seven. The first seven counts sum to 1,764 and
match the retained length-13 census as exact permutation sets after inversion.
The coefficients satisfy `b_n = 3 b_(n-3) + b_(n-5)` for every n >= 14.
These now count the **entire ordinary basis**. They follow from the exact state
equations `F_q = [q=24] + x sum_(q --a--> t) F_t`, together with the global
width theorem; they are not a recurrence fitted to finite data.

The separate [boundary-symmetry theorem](three-three-boundary-symmetry.md)
partitions the complete basis into free 36-element orbits. In generated
orientation one may freely reorder labels 1,2,3 and independently reorder the
final three output positions; the two supports are disjoint in every basis
element. The retained census has 49 canonical cores. These symmetries explain
the factor 36, while the grammar gives the complete longer structure.

## Why width seven is enough

The [global theorem](generalized-basis-width.md) proves, for every positive
r,s, the bound `2 max(r,s)+1`. Fix the lazy schedule and represent each token
by its distinct insertion/removal endpoints. Overlapping tokens admit a single
consistent total stack order, using interval Helly and chordality. A token can
be placed below all the rest exactly when fewer than r intervals cover its
insertion endpoint and fewer than s cover its removal endpoint. Repeatedly
removing any such token is an exact offline recognition rule.

For a basis permutation, its nonrecord interval system is minimally rejected.
Deleting a nonrecord really erases only that interval; deleting a record can
change the lazy schedule and is not assumed to preserve it. If more than
2k nonrecord intervals overlap, where k=max(r,s), take the k earliest starts
and k latest ends. A remaining middle interval can be deleted without making
any forbidden endpoint count allowed. This preserves rejection and contradicts
minimality. At most one record adds one transient held token, giving 2k+1.

Specializing to (3,3) closes the exact global gap left by the
[earlier width-seven construction](three-three-bounded-basis.md). No larger-width
search or finite agreement is needed for this step.

## Evidence, source comparison, and limits


The endpoint rule is an offline existence criterion. No historical-priority
claim is made for it or for the width theorem. The grammar/GF conclusion is
computer-assisted and all-length: finite closure and exact rational identities
are combined with a separate written global exclusion proof. Small exhaustive
checks are corroboration, not substitutes for those arguments.

This is a theorem about the **basis**, not an enumeration of all sortable
permutations. The whole-class algebraicity and its scalar equation are treated separately in the flagship paper. No new

For every fixed positive pair r,s, the [general rational-basis corollary](generalized-basis-rationality.md)
combines the width theorem with the literal finite-state recognizer and the
classical regular one-deletion construction. Thus rational basis enumeration
extends to all fixed widths, though a practical explicit automaton is supplied
here only for (3,3). This still does not enumerate the whole generated class.
