# Claim-by-claim formal scope

Edition: 14 October 2026. These statements concern a single unrestricted-height generalized top-position stack. Push and pop widths are distinct from physical capacity. Generated outputs, sortable inputs and operation histories are different objects; the certificates count distinct permutations and prove the required inversion correspondence.

## Completed headline results

1. **Every fixed positive width pair.** `general-positive-width/` proves exact distinct-output counting and algebraicity over the rational-function field for the actual generated-output and sortable-input series. The endpoints in `StackSorting.GraphWidth.GeneralConstruction` are `stack_uniform_admissibility`, `stack_exact_count`, `stack_output_series_algebraic` and `stack_sortable_series_algebraic`. The counting/algebraicity statements require `0 < r` and `0 < s` and cover every size, including zero. Uniform admissibility and the decomposition/routing/representation witnesses are constructed, rather than assumed. The 607-module source closure includes the geometric width, finite-tree representation, canonical-language and counting connections used by this final theorem.

2. **The actual (3,3) counting series has degree exactly 12.** `actual-scalar-equation/` supplies the 1,613-module all-length count-to-polynomial closure. `actual-count-degree-twelve/` adds the literal-branch, inversion, one-based raw-sortability and exact-degree conclusions. Both actual series satisfy the displayed polynomial without an assumed root identity; their minimal polynomials have degree 12. Every lower-degree annihilator must be the zero polynomial. The ten-coefficient branch condition selects the branch; it is not a substitute for the all-length cardinality proof.

3. **The (2,2) cubic.** The root formal certificate proves original-machine enumeration, the cubic and uniqueness of the constant-term-one branch. This is a structural derivation of a known enumeration, not a claim that the cubic was previously unknown.

## Completed companion results

- **Physical capacity:** the combined root certificate proves minimum physical capacity, exact bounded permutation cardinalities, the recurrence, uniqueness and coefficient stabilization. Capacity includes every transient held token immediately after a push.
- **Infinite bases and threshold:** `unequal/` and `equal/` prove infinite bases for generated and sortable classes for `r,s >= 2` except `(2,2)`, and the sharp threshold `max(r,s)+2`. The finite-side machine characterization is separately stated for positive widths.
- **Finite-side cardinalities:** `basis-cardinality-width/` proves that for positive widths and `H <= max(r,s)+1`, the entire capacity-H basis has exactly `H!` elements, for generated and sortable classes. This includes `H=0`, whose only obstruction is the singleton. The finset formulas hold for every H; identifying them with machine bases requires the capacity bound.
- **Exact family widths:** the same packet proves displacement widths `s+2` for the unequal family, `r+3` for equal family A and `r+2` for equal family B, with the families' stated width hypotheses and all nonnegative family indices. These are displacement identities; they do not assert acceptance of these forbidden permutations.
- **Global basis-width bound:** the `generalized/` sources include the original raw-machine wrapper for one-deletion-minimal rejected inputs at positive widths. The endpoint is `CanSort_oneDeletionMinimal_width_le` in `GeneralizedRawCanSortWidth.lean`; its full source closure is also included in the new `general-positive-width/` replay. The bound is `2 max(r,s)+1`, with standardized one-value deletion and the documented generated/sortable orientation. It does not itself formalize a complete basis grammar or its rational enumeration.
- **Container equivalence:** `container/` proves the positive-width unbounded generation equivalence, with or without bypass, and transfers the infinite-basis conclusion. Simulating a bypass does not preserve a fixed physical capacity.

## Boundaries

The general construction establishes classical existence with coarse parameter-only bounds. It does not extract an efficient algorithm or assert zero-width counting results. Its selector realization constructs a supported tuple; arbitrary optional selector assignments are not a new theorem.

The complete finite grammar descriptions and rational enumeration of the `(2,3)`, `(2,4)` and `(3,3)` bases, general rational basis enumeration, cited finite unbounded classification cases, and analytic capacity pole/Brownian-limit results retain their written-proof scope. Nor does general algebraicity alone certify a particular catalytic recurrence, its complexity bound, a separate quintic's minimal degree, or every auxiliary assertion in the supporting notes.

## Evidence and reproduction

Each packet provides exact source hashes, dependency pins and source-only replay instructions. The new general theorem's independent check rebuilt all 607 project modules and audited 15,372 safe roots and 46,373 dependencies; only `propext`, `Classical.choice` and `Quot.sound` were admitted. The 122 inventoried generated runtime declarations are not permitted unsafe or partial logical dependencies.

The exact-degree review freshly compiled its final joins and verified the inherited counting and branch certificates, including the completed 1,613-module counting replay. It did not repeat that entire inherited rebuild. The public replay instructions allow reconstruction from sources without distributed project objects. Official pinned Lean/mathlib compiled dependencies remain part of the trust boundary.

Release integrity tests check byte consistency. Finite model tests check their finite instances. A packaging pass does not by itself constitute another Lean proof replay. The top-level `VERIFICATION.json` identifies checks actually run for this edition.
