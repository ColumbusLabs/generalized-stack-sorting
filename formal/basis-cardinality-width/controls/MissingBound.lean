import FiniteCapacityBasisCardinality
open StackSorting.Generalized.Unequal
example (p : List Nat) : p ∈ finiteGeneratedBasis 3 ↔ MinimalForbiddenH 1 1 3 4 p := by
  apply finiteGeneratedBasis_exact (by decide) (by decide)
  decide
