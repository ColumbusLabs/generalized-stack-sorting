# Bounded geometric width for top-position stack schedules

This is a structural reduction for the unrestricted permutation class, **not an enumeration or algebraicity theorem**. No novelty claim is made.

## 1. Falsifiable starting question and outcome

The tested sharp candidate was: the proper-overlap graph of every feasible (3,3) lazy schedule has treewidth at most four. It is false. The generated permutation

    6,3,9,5,1,12,7,8,4,2,10,11

has a proper-overlap graph of treewidth exactly five. `treewidth-five-certificate.json` contains a literal legal lazy history, connected disjoint minor branch sets with minimum degree five, and a width-five filled elimination ordering. `verify_treewidth_certificate.py` checks these independently with integer/set operations, not a treewidth library or the normal-form oracle. No minimum-length claim is made.

A different, conservative uniform bound does hold by the argument below. It changes the counting target from unbounded rank words to bounded-treewidth rooted endpoint diagrams. The missing unique finite grammar for those diagrams is explicitly left open.

## 2. Definitions and theorem

Fix positive insertion/removal widths r,s and set k=max(r,s). A schedule gives n tokens with distinct insertion and removal event times a_v<b_v. A legal realization inserts a token in one of the first r positions and removes it from one of the first s positions (top-first, zero-based positions less than r or s). Let I_v=[a_v,b_v].

Define X, the **proper-overlap graph**, on tokens: uv is an edge precisely when

    a_u<a_v<b_u<b_v, or a_v<a_u<b_v<b_u.

Containment is deliberately excluded. The ordinary interval intersection graph has unbounded treewidth even for (1,1), by nested intervals.

Define D, the **endpoint diagram graph**, on the 2n events: consecutive events form a path, and each insertion event is joined to the matching removal event. Optionally add the edge from the final event to the first event, giving a distinguished rooted oriented Hamiltonian cycle for n>=2. The two event types are retained as vertex colors. Parallel edges can be ignored for treewidth; n<=1 is trivial.

**Theorem.** Every realizable top-position (r,s) schedule satisfies

    tw(X) <= 6k-1,       tw(D) <= 12k-1.

In particular unrestricted (3,3) lazy schedules satisfy tw(X)<=17 and tw(D)<=35. The bounds are conservative and no sharpness is claimed. The theorem applies to arbitrary realizable schedules, not only lazy ones.

## 3. A single global physical order

Two tokens held simultaneously keep their relative physical order until one is removed. Orient every edge of the interval intersection graph from its physically upper token to its lower token. This orientation is acyclic.

Indeed, three pairwise-intersecting intervals have a common open time gap, by interval Helly and distinct endpoints. Their orientation is therefore that of a total physical stack order and has no directed triangle. If a shortest directed cycle had length at least four, its underlying interval-graph cycle would have a chord. Either orientation of this chord makes a shorter directed cycle, a contradiction. To see chordality directly, select a cycle interval having the earliest right endpoint. Its two cycle neighbors contain that endpoint, so intersect each other.

Choose a total order extending this acyclic orientation, and give each token v a distinct positive depth y_v, increasing down this order. At every time the physical stack is precisely the restriction of this global order to held tokens. Consequently, at time a_v fewer than r active tokens have y<y_v, and at time b_v fewer than s active tokens have y<y_v. Token v itself is omitted in these counts.

This repeats the global-order lemma of the project's reviewed endpoint-peeling proof (`docs/generalized-basis-width.md`, Sections 1–3); it is included here so the geometric step has an explicit premise.

## 4. Geometric drawing and planarization

Place all event endpoints on the x-axis in their schedule order. In the lower half-plane draw token v by the polygonal U-curve

    (a_v,0) -> (a_v,-y_v) -> (b_v,-y_v) -> (b_v,0).

The two bends are geometric bends only, **not graph vertices**. Distinct x-coordinates for endpoints and distinct y-depths guarantee that all intersections away from the baseline are transverse intersections of exactly one vertical stem and one other token's horizontal segment. There are no coincident stems, coincident horizontal segments, triple crossings, or crossings at bends.

A vertical stem of v intersects exactly the horizontal segments belonging to tokens active at that endpoint and physically above v. Thus its insertion stem has at most r-1 crossings and its removal stem at most s-1 crossings. In particular every stem has at most k-1 crossings. A token's horizontal segment may be crossed arbitrarily many times; **no bounded total-crossings-per-token claim is used**.

Add baseline edges between consecutive event endpoints. For n>=2 add a closing curve from the first to last endpoint outside a rectangle containing all U-curves: leave the first endpoint to the left of every event, descend below every token depth, pass rightward below all curves, then return on the right of every event to the final endpoint. It is disjoint from every existing edge except at its ends. All endpoint vertices are incident with the unbounded upper face; the added outer cycle encloses all token U-curves below the baseline. If preferred, map its enclosed region into a disk with the endpoints on its boundary.

Let P be the plane graph obtained by replacing every transverse crossing by a degree-four vertex. Suppress geometric bends, but do not suppress crossing vertices. Multiple edges do not affect treewidth and may be reduced to single edges when applying the standard theorem.

Every crossing c lies on a particular vertical stem of some token v. Along that stem, the path from its baseline endpoint to c contains at most k-1 crossing vertices and hence at most k-1 edges before and including c. No horizontal crossing is missed: every crossing is on one such vertical stem, even if it is also on a long horizontal portion of another token. Therefore every vertex of P has graph distance at most k-1 from an outer-face endpoint.

**Peeling lemma.** In a plane graph, a vertex at graph distance at most d from an outer-face vertex is removed within d+1 successive deletions of the current outer-face vertices. For the inductive step, after an outer-face vertex is removed, each surviving neighbor becomes incident with the enlarged outer face along the vacated edge/vertex neighborhood. Apply induction along the path. This remains valid for disconnected residual drawings, with the common unbounded face.

It follows that this embedding of P is k-outerplanar.

Use the established theorem that a k-outerplanar graph has treewidth at most 3k-1. The original attribution is Hans L. Bodlaender, *A partial k-arboretum of graphs with bounded treewidth*, Theoretical Computer Science 209 (1998), 1–45, Theorem 83, DOI https://doi.org/10.1016/S0304-3975(97)00228-4. A primary complete proof and algorithm are available in Ioannis Katsikarelis, *Computing bounded-width tree and branch decompositions of k-outerplanar graphs* (2013), Theorem 3.8, https://arxiv.org/pdf/1301.5896 . This is an invocation of that established theorem, not a new outerplanarity/treewidth claim.

Hence P has a tree decomposition whose bags have at most 3k vertices.

## 5. Lifting bags to token intersections

For each planarization vertex q, let L(q) be its token-label set. At an original endpoint this is the single incident token; at a crossing it is the two crossing tokens. Thus |L(q)|<=2.

Replace every tree-decomposition bag B by the union of L(q) over q in B. New bags have size at most 6k. These bags form a tree decomposition of the geometric token-intersection graph Y:

- Every token appears, since its two endpoints occur in P's bags.
- An edge uv of Y has an actual crossing q. Any bag containing q lifts to a bag containing both u and v.
- For a fixed token v, its U-curve becomes a connected path of vertices and edges in P. For each vertex q on that path, bags containing q form a connected subtree. For two consecutive path vertices, those subtrees intersect because some bag contains their common edge. Their union is consequently connected. This union is exactly the set of lifted bags containing v, proving running intersection.

Y need not equal X. Contained intervals can produce two U-curve crossings when the inner token is placed below the outer token. Nevertheless X is a subgraph of Y: if a_u<a_v<b_u<b_v, then either v lies lower, giving a crossing on v's insertion stem, or u lies lower, giving a crossing on u's removal stem. Thus every proper-overlap edge is covered. Deleting extra edges cannot increase treewidth. This proves tw(X)<=6k-1.

## 6. Lifting bags to endpoint diagrams

For each planarization vertex q replace it instead by **both original endpoints of every token in L(q)**. Each q contributes at most four endpoint vertices, so bag sizes are at most 12k.

For a token's matching edge, every bag containing any point of its planarized path now contains both original endpoints. A baseline/closing-cycle edge already has its endpoint pair in a bag of P, so the lifted bag contains that edge as well. The bags containing either original endpoint of token v are exactly the union of P-bag subtrees along v's connected path, which is connected by the same argument as above. All endpoints are covered. Thus these bags form a tree decomposition of D of width at most 12k-1.

This is a treewidth statement about the **time-ordered endpoint diagram**. It is not asserted for the usual permutation incidence graph (the union of numerical and output adjacency paths); that graph is different.

## 7. Exact permutation encoding and the unresolved counting obligation

A generated permutation determines one lazy endpoint diagram. At a new record v, insert the unread labels through v in increasing order, then remove v. Otherwise remove the requested held label. Record endpoints remain separate events. Labels themselves can be recovered from the matching: enumerate insertion vertices from left to right as 1,...,n, and read their matched labels at removal vertices.

Conversely, take a rooted oriented endpoint cycle/path with insertion/removal colors and a perfect matching from insertion to a later removal. Require that every maximal consecutive insertion run is immediately followed by the removal matched to the run's final insertion. This is precisely the lazy-record condition. Reading the matched labels at removal vertices gives a unique permutation and its unique lazy schedule. Therefore no physical-history multiplicity appears in this endpoint encoding.

The unrestricted G(3,3) counting problem can consequently be restated exactly as counting those lazy endpoint diagrams that admit a top-three realization; all lie in the fixed treewidth-35 class just proved. This is a concrete bounded-interface **graph** target, rather than a claim that a bounded number of scalar rank-word completion profiles suffice.

What is missing is a canonical, size-preserving, finite-state tree or multiple-context decomposition of these diagrams that:

1. represents each lazy endpoint matching exactly once;
2. recognizes realizability under decomposition without choosing a physical order multiple times;
3. preserves the distinguished endpoint order and matching correlations; and
4. yields a proper finite polynomial generating-function system.

The existence of bounded-width decompositions alone does not provide such a grammar. Different legal physical orders, planarizations, and tree decompositions can describe the same permutation. Counting them would repeat the original history-overcount problem. General graph dynamic programming on a single input diagram does not enumerate the family of distinct diagrams. No invocation of Courcelle's theorem, no bound on graph treewidth, and no finite coefficient test fills this gap.

The structural theorem rules out unbounded graph-separator size as a necessary obstruction in this representation. It neither proves algebraicity nor nonalgebraicity. This route's present outcome is the width reduction and the certified rejection of its overly sharp initial candidate.
