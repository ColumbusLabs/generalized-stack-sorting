# Exact clause valuation for unrestricted completion counts

This is a proposed all-length reduction to signed words over Z,B,T, not a finite transfer theorem or the requested algebraic equation itself.

## 1. Statement

Use completion counts c(S,n) for h initially held labels and exactly n later increasing input labels, as in o-run-counting-quotient.md. All tokens must eventually be output and each distinct output is counted once. Let P and Q be normal-form factor words with no O. Require P nonempty and every state below to satisfy the ambient first-coordinate and second-coordinate bounds. Clauses may occur in P and Q. For m>=2 and nonempty J subset {1,...,m}, let w_J be the length-m word having Z at positions in J and B elsewhere.

**Candidate theorem.** For all n>=0,

    c(P C_m Q,n)
       = sum_{empty != J subset {1,...,m}}
              (-1)^(|J|+1) c(P w_J Q,n).

The same identity holds for the formal completion series C_S(x). In a noncommutative notation for context substitution, it is

    C_m = B^m - (B-Z)^m.

This is a linear identity of completion counts in every permitted context, not equality of physical stack sets or labelled continuation languages with signed multiplicity. The already-O-run relabelling reduces every reachable state to the stated O-free case. Applying the identity repeatedly then expresses its count as a finite signed combination of ordinary Z/B/T words of the same held height. This reduction alone does not prove finite dimensionality of the resulting word series.

## 2. A clause is a precedence restriction on its final label

Consider a nonempty prefix P with labels 1,...,a, and append m binary coordinates for labels a+1,...,a+m. Denote the original physical top of P by t. If all m coordinates are 1, t remains on top throughout, so t precedes the final label a+m.

If at least one appended coordinate is 0, its new token is inserted above every old-prefix label. From that moment on t has physical position at least one. Every subsequent slot-0 or slot-1 insertion is above t; in particular the final appended label is above t. It is therefore above every label of P. This also holds if the first zero is the final coordinate itself.

Consequently C_m is exactly B^m together with the requirement

    label a+m is physically above every label 1,...,a.

Later maximum insertions do not change relative orders among these tokens. Hence the equivalence remains true with arbitrary suffix Q. For several clauses, impose this precedence requirement separately for each clause's final label and its entire earlier-label prefix.

## 3. A monotone bottom-elimination model for a fixed continuation

Fix one prospective complete output permutation omega on h old labels and n future labels. Use its lazy future-input schedule: initially all h old tokens are present, and future input arrives in its numerical order. The known adjacent-swap normalization applies while leaving the initially held stack unchanged. Alternatively any fixed schedule equivalent to omega may be used after this normalization.

Associate an interval with each token, extending every old token from a common initial boundary to its output. Insertions of old tokens have no slot requirement because the initial physical stack is supplied. Future insertions and every output have the top-three slot bound. The global-order lemma remains valid: simultaneously present tokens keep their relative order; the interval graph is chordal; and the resulting acyclic orientation extends to one total physical order. Conversely such a total order realizes the future schedule by restriction to currently present tokens.

A normal-form word with no O imposes the following additional conditions on that total order restricted to old labels:

- At a Z coordinate j, no smaller old label precedes j physically.
- At B, at most one smaller old label precedes j.
- At T, at most two smaller old labels precede j.
- Replace each C_m by B^m and add its final-label precedence condition from Section 2.

These are exactly its coordinate-language conditions, including every clause. To construct a total order from bottom to top, let U be the remaining tokens. A token is eligible if it satisfies all applicable requirements when placed below U minus itself:

1. Its future insertion/output endpoint counts among U meet the slot bounds (omit the insertion check for an old token).
2. If it is an old label j, the number of smaller old labels in U meets its coordinate upper bound.
3. If j is the final label of a clause, no old label preceding that clause remains in U.

Every requirement is monotone under removing other tokens. More directly, placing an eligible token below a realizing order of the rest preserves every other token's inequalities and precedences. Thus the exact bottom-deletion argument applies: feasibility is equivalent to every nonempty token subset having an eligible token. If greedy elimination stops, its nonempty residual is a certificate of infeasibility; any realizing order restricted to that residual would have an eligible bottom token.

The proof uses a total physical order only as an existence certificate. It does not count physical orders or histories.

## 4. Forced-zero faces have the required intersection property

Start from the base state P B^m Q and fix omega. For J subset {1,...,m}, forcing each j in J to Z lowers the corresponding old-coordinate bound from one to zero. All other requirements, including clauses in P and Q and the entire future schedule, remain unchanged.

We claim:

    omega is feasible from every single-zero face P w_{ {j} } Q, j in J
    if and only if
    omega is feasible from P w_J Q.

The reverse implication is immediate by relaxing constraints. For the forward implication suppose all single-zero faces are feasible but the joint face is not. Section 3 gives a nonempty residual U with no jointly eligible token. The base state is feasible because any one single-zero face is feasible. Therefore U has a base-eligible token.

A base-eligible token can lose eligibility on adding the Z restrictions only when it is one of the selected old labels and has exactly one smaller old label in U. There is at most one such label: the second-smallest old label remaining in U. Thus all base-eligible tokens in U consist of one selected label j. Imposing only that one Z restriction already leaves U with no eligible token. This contradicts feasibility of the j single-zero face. The claim follows.

The argument permits arbitrarily many new tokens and arbitrary additional O-free factors and clauses outside the displayed block. Their eligibility requirements are unchanged. In particular it does not infer an intersection-of-output-languages identity from an intersection-of-initial-stack-sets identity without proof.

## 5. Inclusion-exclusion counts distinct outputs

As physical stack sets, P C_m Q is the union of the m single-zero faces: the binary block must contain at least one zero. Therefore its admitted complete output language is the union of the m admitted single-zero output languages. Section 4 says that every nonempty intersection of these output languages is exactly the language of the corresponding joint-zero face.

For each fixed n these are finite sets of output permutations on the same labelled universe. Ordinary inclusion-exclusion gives precisely the formula in Section 1. It counts each admitted output once, regardless of its number of initial stack choices or physical histories. Summing over n gives the formal-series identity coefficientwise.

## 6. Scope and dependencies

This candidate uses the exact normal form, the global-order/bottom-deletion argument for fixed schedules, and the O-run counting relabelling. Section 3 explicitly extends the endpoint model to a supplied initial stack set; that extension is established in that section. Section 2 supplies the clause-to-precedence equivalence rather than assuming generic Boolean intersections are preserved.

The resulting signed three-letter recursion still admits long suffix rewrites. No six-state matrix upper bound, finite first-return system, selected algebraic branch, minimal polynomial, historical priority, or Lean certification is claimed here.
