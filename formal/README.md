# Formal certificates

All certificate families use Lean 4.34.1. Their scopes are distinct.

- `actual-scalar-equation/`: 1,613 original project modules. The endpoints `literal_G_counts` and `actual_counts_literalQ` identify the all-length cardinality of distinct generated outputs of the literal `(3,3)` machine and establish its scalar polynomial relation. This closure uses Lean Core/Std without mathlib. It does not formalize the all-width MSO argument, irreducibility, degree minimality, sortable-input inversion, or analytic asymptotics.
- Root-level files: the 25-module `(2,2)` enumeration closure and its 38-module combined physical-capacity extension, with mathlib pinned by `lake-manifest.json`. The capacity extension includes exact bounded cardinalities, the recurrence, uniqueness and coefficient stabilization; it excludes the pole analysis and Brownian-limit application.
- `generalized/`, `unequal/`, `equal/`, `container/`: Core/Std certificates for the stated obstruction families, finite-side characterizations and unbounded-capacity container transfer. The exact family-width equalities, finite-cardinality deduction and cited finite cases remain written results. The bypass simulation is not a fixed-physical-capacity equivalence.

See the individual paper's formal-verification section for theorem-level scope. Integrity verification and finite tests are not fresh Lean compilations.
