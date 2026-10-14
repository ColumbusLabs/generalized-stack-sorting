# Formal certificates

All certificate families use Lean 4.34.1. Their scopes are distinct.

- `actual-scalar-equation/`: 1,613 original project modules. The endpoints `literal_G_counts` and `actual_counts_literalQ` identify the all-length cardinality of distinct generated outputs of the literal `(3,3)` machine and establish its scalar polynomial relation. This closure uses Lean Core/Std without mathlib. This original packet proves the scalar identity. The general and exact-degree packets below supply the later all-width, inversion and minimal-degree results; analytic asymptotics remain outside these certificates.
- `general-positive-width/`: complete construction and counting/algebraicity chain for every positive integer width pair, including the empty permutation. Its 607-module closure constructs uniform admissibility rather than assuming it. The result gives classical existence with parameter-only bounds, without an efficient extracted algorithm or a zero-width counting claim.
- `actual-count-degree-twelve/`: completed original-machine `(3,3)` generated/sortable cardinality, literal-branch identity, irreducibility and exact minimal degree 12, including the nonzero-annihilator lower bound.
- `basis-cardinality-width/`: exact finite-side basis cardinalities and explicit obstruction-family width equalities, extending the earlier classification certificates.
- Root-level files: the 25-module `(2,2)` enumeration closure and its 38-module combined physical-capacity extension, with mathlib pinned by `lake-manifest.json`. The capacity extension includes exact bounded cardinalities, the recurrence, uniqueness and coefficient stabilization; it excludes the pole analysis and Brownian-limit application.
- `generalized/`, `unequal/`, `equal/`, `container/`: Core/Std certificates for the stated obstruction families, finite-side characterizations and unbounded-capacity container transfer. The added `basis-cardinality-width/` packet supplies exact family widths and finite-side cardinalities. The cited finite unbounded cases remain written results. The bypass simulation is not a fixed-physical-capacity equivalence.

See the individual paper's formal-verification section for theorem-level scope. Integrity verification and finite tests are not fresh Lean compilations.

[The claim matrix](CLAIMS.md) connects the public statements to these distinct certificates and identifies remaining written results. Each release source is hash-bound; an integrity check is not a new proof replay.
