# Explicit endpoint-class MSO sentence and bijection

Supporting expansion for frozen candidate v3, 10 October 2026. This note introduces no additional relation to the counted structure. The vocabulary is exactly unary I,R and binary S,M. All relation predicates below are abbreviations for formulas in that vocabulary. Graph treewidth refers only to the undirected union of S and M.

## 1. Path and time

For a binary relation E, define reachability including equality by

    Reach_E(x,y) := forall Z [
       (Z(x) and forall p,q ((Z(p) and E(p,q)) -> Z(q))) -> Z(y)].

Require the universe to be nonempty and S to be a directed Hamiltonian path. One explicit sentence chooses a vertex f with no incoming S-edge, requires every vertex reachable from f, every vertex to have at most one outgoing S-neighbor, and every vertex other than f to have exactly one incoming S-neighbor. This forces a finite directed path containing all vertices; it excludes loops, directed cycles and extra edges. Set

    x<y := x!=y and Reach_S(x,y).

The dense relation < is never an input relation or a graph edge. It is used only as this fixed MSO abbreviation. Recovering it during tree decoding uses MSO backwards translation of this formula, not an augmentation of the bounded-width graph.

## 2. Event colors and perfect matching

Require exactly one of I(x),R(x) for every vertex x. Require M symmetric and every vertex to have exactly one M-neighbor, of the opposite color. For every matching pair with I(x) and R(y), require x<y. These axioms make M a loopless perfect forward insertion/removal matching.

Require the lazy-boundary axiom

    forall x,y [(I(x) and R(y) and S(x,y)) -> M(x,y)].

The malformed three-event path R,I,R with only its last two vertices matched is excluded because the first R has no matching partner. An extra uncolored vertex or a doubly colored vertex is excluded by the partition axiom. A backward pair is excluded by forwardness. The empty universe is excluded here; its permutation contribution is added separately.

## 3. Fixed-width feasibility, without a physical-order quantifier

Let U be a monadic set variable containing only insertion vertices. Define

    A(U,u,x) := U(u) and exists z [M(u,z) and u<x and x<z];

    B(U,u,x) := U(u) and exists y,z [M(x,y) and M(u,z)
                                                   and u<y and y<z].

For fixed positive r,s, Eligible(U,x) is U(x) together with

    not exists u_1,...,u_r [all u_i distinct and all A(U,u_i,x)],
    not exists v_1,...,v_s [all v_i distinct and all B(U,v_i,x)].

The feasibility sentence is

    forall U [((exists u U(u)) and forall u (U(u)->I(u)))
                  -> exists x Eligible(U,x)].

There are only finitely many first-order witnesses because r,s are fixed. No binary set variable, order guess or physical history is quantified. By the exact endpoint-peeling theorem this sentence is equivalent to realizability of the complete fixed schedule.

## 4. Bijection with lazy permutation diagrams

Label insertion vertices 1,...,n in S-order. Each removal has exactly one insertion partner, so reading partner labels along removals yields a permutation of [n]. Consider any maximal consecutive insertion run. It must be followed by a removal: the final event cannot be an insertion because its matched removal lies later. Its final insertion is matched to the immediately following removal by the lazy-boundary axiom. Thus that output is the largest label inserted so far, and is larger than every earlier output. The run starts at the first unread label and ends exactly at this new output maximum. Between these insertion runs, outputs remove only already inserted values. Consequently the event word and all matching pairs coincide with the unique lazy schedule obtained from this permutation.

Conversely, construct the lazy schedule of any permutation by reading through the next output value precisely when it has not yet been read, then outputting it. This produces the partition, Hamiltonian path, perfect forward matching and lazy-boundary condition above. These two constructions are inverse up to the unique time-order-preserving isomorphism.

A generated permutation has a feasible lazy schedule by the adjacent-operation commutation lemma. A feasible lazy diagram is itself a valid generating schedule. Hence the feasible structures defined above are in bijection with the generated permutations, rather than with their possibly many physical histories.
