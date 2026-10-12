# A global width bound for generalized-stack bases

This is separate from the already-reviewed bounded-width automaton result. No novelty or formal certification is claimed.

## Theorem

Fix positive top-position widths r,s and put k=max(r,s). Every basis element of the increasing-input generated class G(r,s) has lazy width at most 2k+1. Equivalently, every sortable-input basis element p satisfies

    1 + max_i(i-p_i) <= 2 max(r,s) + 1.

In particular the whole (3,3) generated basis has width at most seven. The 28-state width-seven basis DFA is therefore a complete all-length basis description, and the COMPLETE basis generating function is

    B_(3,3)(x) = 36 x^7 (1+3x+2x^2+3x^3+x^5-x^6)/(1-3x^3-x^5).

The inverse sortable-input basis has the same counts. This does not establish algebraicity of the class of all (3,3)-sortable/generated permutations.

## 1. Schedules and interval endpoints

A schedule specifies each individual insertion and removal and their token labels, but not their physical stack slots. Its endpoints are distinct integer event indices. Token v's insertion occurs at a_v and its removal at b_v>a_v; associate I_v=[a_v,b_v]. Distinct endpoints never coincide.

Two intervals overlap exactly when their tokens are held together during an open gap between events. Set

    A(v) = {u != v : a_u < a_v < b_u},
    B(v) = {u != v : a_u < b_v < b_u}.

These count the other tokens active at v's insertion/removal. An interval strictly contained in I_v lies in neither set, while an interval containing I_v lies in both.

For a generated-output permutation use its lazy schedule: before the next new record v, insert every unread input through v, one at a time in increasing order, and then remove v; for a held output, remove it without reading anything. The record's own insertion/removal remain two distinct consecutive events, and its transient height counts. The repository's arbitrary-width normalization lemma proves that generation is equivalent to realization of this fixed lazy schedule.

## 2. Every realizable schedule has a global stack order

In a legal physical history, two simultaneously held tokens never change their relative order. Orient each edge of the interval intersection graph from the upper token to the lower token. This orientation has no directed triangle: three pairwise-intersecting intervals have a common intersection by the interval Helly property; since all endpoints are distinct, their common intersection contains an open time gap where all three tokens coexist and physical stack order is transitive.

It also has no longer directed cycle. Choose a shortest directed cycle. Its underlying undirected cycle, if of length at least four, has a chord because interval graphs are chordal. Either orientation of that chord gives a shorter directed cycle along one of the two directed portions of the old cycle. This contradicts minimality.

An elementary chordality argument suffices here. Among intervals of an alleged chordless cycle choose one whose right endpoint is smallest. Its two cycle neighbors both intersect it and end later, so they both contain that right endpoint and hence intersect each other, providing a chord.

The orientation is thus acyclic and extends to a total order on all tokens. At every time, the physical stack equals that total order restricted to the held tokens. Conversely, any total order whose restricted insertion/removal depths meet the slot bounds realizes the schedule by using those restricted positions. This includes schedules obtained by erasing arbitrary tokens, whether or not the shortened schedule is lazy.

## 3. Bottom deletion is an exact recognition rule

For a subset U of remaining intervals call v in U eligible when

    |A(v) intersect U| < r  and  |B(v) intersect U| < s.

The schedule is realizable if and only if repeatedly deleting an arbitrary eligible interval eventually deletes every interval.

Proof. A realizing total order has a bottom interval v, whose insertion depth is exactly |A(v) intersect U| and whose removal depth is exactly |B(v) intersect U|. Thus it is eligible. More strongly, deleting ANY eligible v preserves realizability in both directions. Erasing v from a realizing order gives one direction. For the other, take a realizing order of the remaining intervals and place v below all of them. Other endpoint depths are unchanged, and v's own depths satisfy the two displayed inequalities. This proves equivalence at every deletion step. If a nonempty U has no eligible token, no realizing total order can have a bottom token, so it is rejected. QED.

The resulting endpoint-peeling rule is offline and uses the whole schedule; it is not a claim that an online first-larger insertion policy is complete. Existing generalized-stack recognition algorithms must be compared before making any novelty claim about this reformulation.

## 4. Records and nonrecords behave differently under deletion

A record token has two consecutive endpoints. Its interval covers no endpoint of any other token, so it occurs in no A(u) or B(u) for u different from it. Removing every record interval therefore does not alter any endpoint count for any nonrecord interval. Moreover records can always be restored above all nonrecords: their intervals are pairwise disjoint and each is inserted and removed at slot zero. Thus a lazy schedule is realizable if and only if its NONRECORD interval subsystem is realizable.

Deleting a NONRECORD value v from the output permutation leaves all other record/nonrecord decisions unchanged after standardization. All other labels first arrive at the same surviving record boundaries: v was not itself one of those boundaries. Consequently the shorter lazy schedule is precisely the old schedule with v's insertion/removal erased, up to order-preserving reindexing of event times. After also erasing record intervals, its interval subsystem is the old nonrecord subsystem with I_v removed.

Now let p be a basis element. Its nonrecord subsystem J is rejected, but J minus ANY ONE interval is realizable, because every such permutation deletion is generated and the preceding paragraph applies. Hence J is a vertex-minimal rejected interval subsystem. In particular it has no eligible interval: deleting an eligible interval preserves rejection by Section 3, a contradiction. This argument does not assume that deleting a record preserves the schedule; that is generally false and is not used.

## 5. A vertex-minimal rejected subsystem has overlap at most 2k

Suppose a rejected subsystem J is vertex-minimal and has 2k+1 intervals simultaneously active at some time T that is not an endpoint. Let K be any such set of 2k+1 intervals. In K, let L be the k intervals with earliest left endpoints, and R the k with latest right endpoints. Since |L union R| <= 2k, choose v in K outside their union.

We claim that deleting v cannot make ANY endpoint count cross from forbidden to allowed. Consider an endpoint t of another interval u that is covered by v; these are the only counts that decrease.

* If t<T, every interval in L starts strictly before v starts, hence before t, and ends after T, hence after t. Thus all k intervals of L strictly cover t, in addition to v.
* If t>T, every interval in R starts before T, hence before t, and ends strictly after v ends, hence after t. Thus all k intervals of R strictly cover t, in addition to v.

The interval u itself cannot be any of these k covering intervals, since an interval does not strictly cover its own endpoint. So the endpoint count before deletion is at least k+1, and after deletion at least k. Since r<=k and s<=k, that endpoint remains above its respective allowed threshold r-1 or s-1. Unaffected endpoint counts do not change.

Initially every interval of J is ineligible (Section 4, or the same eligible-deletion argument for vertex minimality). It has at least one forbidden endpoint count. Every surviving interval still has such a count after v is deleted. The remaining subsystem therefore has no eligible interval and is still rejected by Section 3. This contradicts vertex minimality. Thus simultaneous nonrecord overlap is at most 2k. QED.

## 6. Convert overlap to physical width

In a lazy schedule records are present only during their consecutive insertion/removal pair; at most one record is held at any time. At all other times the held tokens are nonrecords. Section 5 bounds their number by 2k, so the entire physical height is at most 2k+1.

The lazy schedule's maximum physical height is exactly

    w(p) = 1 + max_i(p_i-i)

in generated orientation: the maximum is attained just after a new record is inserted, when precisely p_i-(i-1) tokens are held. Thus w(p)<=2k+1 as claimed. Inversion sends generated basis elements to sortable-input basis elements and turns the displayed displacement into 1+max_i(i-p_i), giving the input formulation.

For r=s=3 this is seven. The width-seven automaton recognizes exactly actual ordinary basis elements of that width bound, not capacity-only obstructions. The bound therefore upgrades its language and rational function to the complete basis.

## 7. Evidence and attribution boundary

The mathematical argument is Sections 1–6. Small agreement is only corroboration: endpoint peeling matches the literal (3,3) subset recognizer on all 46,234 permutations through length eight. All 1,764 retained basis elements have no initially eligible interval. A targeted randomized minimization of 5,000 width-at-most-nine inputs of lengths 18–40 found no wider basis element; this is expressly not an exclusion proof.

The general recognition reformulation is not asserted to be historically new. Atkinson's defining paper is Generalized stack permutations (1998), DOI 10.1017/S096354839800354X. The project-specific argument is the vertex-critical interval reduction and resulting global basis-width theorem; no priority claim is made about recognition.
