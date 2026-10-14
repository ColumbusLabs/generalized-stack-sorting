import FiniteCapacityBasisCardinality
open StackSorting.Generalized.Unequal
example : (finiteGeneratedBasis 3).card = 7 := by simpa [Nat.factorial] using finiteGeneratedBasis_card 3
