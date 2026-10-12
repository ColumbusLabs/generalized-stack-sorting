# A finite-state description of the width-seven (3,3) basis

No global width bound, full-basis classification, novelty, external peer review, or formal certification is claimed.

## Result and scope

Work with one top-position (3,3) stack: push at zero-based slot 0, 1, or 2 when present, and pop at slot 0, 1, or 2. Let G be the permutations generated from increasing input. Sortable-input basis elements are their inverses.

For a nonempty generated-orientation permutation p define its lazy width by

    w(p) = 1 + max_i(p_i-i).

This definition applies even to rejected permutations. It is the height of the unique lazy input/output schedule, not a claim of a legal restricted history.

The construction below gives an exact finite automaton for the basis elements of G having width at most any specified finite H. At H=7, finite exploration gives 18,971 reachable candidate states, 65 states that can reach acceptance, and a minimal partial DFA with 28 live states (plus an implicit rejecting sink). The verified rational length generating function is

    B_7(x) = 36 x^7 (1+3x+2x^2+3x^3+x^5-x^6) / (1-3x^3-x^5).

Its coefficients at lengths 7 through 13 are

    36, 108, 72, 216, 324, 288, 720.

These match the full retained exhaustive census, both as counts and as permutation sets (see verification packet). Thus this automaton structurally describes all 1,764 currently retained short basis elements and infinitely many longer ones. It also gives the width-at-most-seven counts 1,044, 1,080, 2,484 at lengths 14, 15, 16. These latter numbers are NOT asserted to be the unrestricted basis counts.

For n >= 14 the coefficients of this bounded-width slice satisfy

    b_n = 3 b_(n-3) + b_(n-5).

This is a consequence of the exact finite-state certificate, not a fitted recurrence.

## 1. Output codes and the literal stack-order automaton

Use the unique code alphabet N_b and H_k. At an output boundary let M be the largest value read and let the held values be listed in increasing order.

* N_b reads the next b increasing labels and emits the last one; b is positive.
* H_k emits the kth smallest held label.

The held height changes from h to h+b-1, or h-1, respectively. The physical width constraint for N_b is h+b <= H. Codes begin and end at height zero. Decoding in increasing labels is unique and code length equals permutation length.

Lazy normalization is the repository's previously proved arbitrary-width push/pop exchange lemma. For r=s=3 the record token itself can always be pushed and popped at slot zero. It leaves the held stack unchanged. Conversely, any lazy record step leaves exactly an order attainable by inserting its first b-1 new labels in top-three slots. Thus the literal recognizer state is a set S of orders of the held ranks 1,...,h, starting from {()}.

For N_b insert new maximum ranks h+1,...,h+b-1 successively in every legal top-three slot and take the union. For H_k retain only orders with rank k among their first three entries, remove that entry, and standardize the remaining ranks. An empty set is permanent rejection. Induction on code length proves this is the exact set of reachable lazy physical stack orders. This argument does not use the two-push composition theorem.

At fixed H only h <= H-1 occurs at output boundaries. Each state is a subset of a finite symmetric group, hence this is a finite deterministic recognizer. At H=7 its reachable nonempty state sets number 242, divided by held height as 1,1,3,12,45,90,90.

## 2. Track every one-entry deletion exactly

A candidate basis code is processed together with one shadow for every token already read in its original schedule. Each shadow chooses one token to delete. A shadow consists of:

* the shorter permutation's current literal recognizer state;
* one annotation on every currently held ORIGINAL token, in increasing order: R if retained and already read by the shortened lazy schedule; U if retained but not yet read there; D for the chosen deleted token, until it is emitted originally.

There is at most one D. A shadow with no D still remembers that its selected deletion has already occurred; it must not choose again. No selection flag is needed in the representation because only already-selected shadows are stored.

Initially there are no shadows. On original N_b, append b U annotations to every existing shadow. Also create b new shadows, one for each newly read token: their original old held labels are all R, exactly one new token is D, and all other new tokens are U. Each new shadow starts with the original recognizer state before the N_b step. This initialization is exact: deleting a token not yet read cannot change any earlier relative order or earlier lazy schedule, after standardization.

Process the original output's annotated position (the final newly appended token for N_b, or held rank k for H_k):

* D: emit no shortened letter.
* R: emit H_j, where j is its rank among R annotations.
* U: emit N_j, where j counts the U annotations no greater than this token; change all those U annotations to R first.

Then remove the original output annotation. D is ignored in all shortened ranks and counts. Apply each emitted letter to the shadow's literal recognizer.

This is the exact lazy code of the standardized deletion. In particular, when a record is deleted its remaining batch stays U until a later retained output forces that batch to be read. One must not merely delete a code letter. Induction proves the annotation and shortened-state invariant. The temporary annotation list has length at most H, so the shadow types are finite. Identical shadows can be merged: they have identical future behavior under every original continuation, and acceptance requires the universal condition that none rejects.

Discard a candidate prefix immediately if any shadow rejects. Such a shadow can never regain a generating history in any continuation. At a complete original code, accept precisely when the original recognizer has rejected and every deletion shadow has survived. Because all labels have been read and all original annotations are then gone, surviving shadow states are empty-stack accepting states. Pattern closure makes this exactly minimal forbidden membership.

The shorter schedule cannot exceed H: deleting a token cannot increase lazy width (the repository's existing displacement/deletion lemma). Equivalently this follows from the annotations since every shortened token currently held or introduced at a shortened record corresponds to an original held or just-read token.

## 3. Three justified pruning rules

The implementation uses the following language-preserving restrictions specifically for basis elements.

1. No N_1 occurs. Such a record inserts and immediately removes one token without altering any held order. Deleting it gives the same recognizer-state path with this identity step omitted, so a rejected permutation containing it is not minimal.
2. Do not continue after returning to height zero. Such a prefix is a direct-sum component. Generated permutations are closed under direct sum, by concatenating histories. If a rejected permutation has at least two nonempty components, at least one component is a smaller rejected pattern. Hence basis elements are sum-indecomposable.
3. After the first original failure, no N_b may occur. The first failure is necessarily a held pop. A future record is not read at that failure; deleting that record leaves the earlier failed output prefix unchanged. It therefore witnesses nonminimality. Thus a basis element has read all input at its first failed pop.

The last rule is ONLY terminal input localization, not a claim that exactly four labels remain at failure or that a bounded-width theorem follows.

These prunings leave a finite directed graph. A state records original held height, original recognizer state (or rejecting sink), and the set of deletion shadows. The accepting state is the rejected original empty height with all shadows successful. Breadth-first exploration followed by ordinary reverse reachability removes states with no accepting continuation. DFA minimization preserves the resulting language.

## 4. The 28-state grammar

The file evidence/basis-dfa-width-7.json is a complete partial DFA. Start at 0, accept at 24. A missing transition rejects. N_b and H_k carry the unique output-code meanings above. Every edge emits one output value. This is also a finite right-linear grammar: for each transition q --a--> t add q -> a t, and add 24 -> empty.

The only cyclic strongly connected component contains states 10,14,16,18,21,22,25,27. It is the source of the infinite family structure. All other states describe finite seeds, terminal obstructions, and free final-output permutations. The grammar specifies actual permutations by unique decoding, rather than just their counts.

For each state q let F_q(x) count accepted continuations. Its exact equations are

    F_q = [q=24] + x sum_(q --a--> t) F_t.

The rational certificate supplies all 28 F_q and checks every equation as a polynomial/rational identity. Their power-series solution is unique since every nonconstant transition has a factor x. Evaluating F_0 gives B_7 above. This supplies an algebraic certificate independent of fitting any finite coefficient sequence.

## 5. Free boundary symmetries and the 49 short cores

For any top-position (r,s) stack, membership is invariant under reordering its first r input tokens, and under reordering its last s output tokens.

For the input assertion, take a successful history and stop immediately after its rth input is inserted. List the tokens output before that moment in their output order, followed by the held stack order at that moment. This is an ordering of the first r tokens. Starting with ANY ordering of these r inputs, top-r insertion can build any desired final order: insert the successive tokens in their positions in that target order restricted to the tokens currently inserted. Thus build the listed order first, pop its earlier-output prefix from slot zero, and continue the old history after its rth insertion. This constructs the same output. Apply the argument in both directions. The case of fewer than r total inputs is even simpler.

For the output assertion, stop before the final s outputs. At most s total tokens remain, including unread ones. Insert all unread tokens at slot zero. Every held token is now accessible in the first s positions, so finish in any requested order.

These operations preserve basis minimality: any deletion of a reordered permutation is obtained from the corresponding original deletion by shuffling at most its first r inputs or last s outputs. For increasing-input generated permutations, the first operation becomes arbitrary relabelling of values 1,...,r; the second permutes the final s output positions.

For (3,3), the retained census has no values 1,2,3 in its last three positions. Thus each orbit under these two disjoint free S_3 actions has 36 elements. Canonicalize by making labels 1,2,3 appear in that order, then sorting the last three outputs. Exactly 49 cores remain, with counts by lengths 7..13 equal to 1,3,2,6,9,8,20. The packet lists them explicitly.

This observed disjointness suffices for the 49-core census claim. A stronger all-length boundary-disjointness lemma is not needed for the finite-state theorem and is not assumed here.

## 6. What remains open here

The actual unrestricted basis may contain elements of width at least eight. Neither the retained census, the existing length-16/17 infinite families, nor this exact width-seven DFA proves otherwise. The rational function counts precisely the width-seven slice. It does not establish rationality of the entire basis or algebraicity of the whole sortable/generated class.

A complete classification would require either a proof of a uniform bound (and a sufficiently large exact automaton), or a structural description that handles genuinely unbounded widths. This packet supplies a concrete benchmark and a small exact grammar to challenge either route.
