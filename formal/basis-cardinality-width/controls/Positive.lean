import FiniteCapacityBasisCardinality
namespace CompanionReview
open StackSorting.Generalized.Unequal
example : (finiteGeneratedBasis 0).card = 1 := by simpa using finiteGeneratedBasis_card 0
example : (finiteSortableBasis 0).card = 1 := by simpa using finiteSortableBasis_card 0
example : [0] ∈ finiteGeneratedBasis 0 := by simp [mem_finiteGeneratedBasis]
example : MinimalForbiddenH 1 1 0 1 [0] :=
  (finiteGeneratedBasis_exact (r:=1) (s:=1) (H:=0) (by decide) (by decide) (by decide) [0]).mp (by simp [mem_finiteGeneratedBasis])
example : (finiteGeneratedBasis 3).card = 6 := by simpa [Nat.factorial] using finiteGeneratedBasis_card 3
example : (finiteSortableBasis 3).card = 6 := by simpa [Nat.factorial] using finiteSortableBasis_card 3
example (p : List Nat) : (∃ n, MinimalForbiddenH 1 2 3 n p) ↔ p ∈ finiteGeneratedBasis 3 :=
  finiteGeneratedBasis_all_sizes (by decide) (by decide) (by decide) p
end CompanionReview
