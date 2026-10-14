import ObstructionFamilyWidths
namespace StackSorting.Generalized
example : Unequal.family 2 3 0 = [4,0,2,7,1,3,5,6] := by decide
example : generatedDisplacementWidth (Unequal.family 2 3 0) = 5 := by decide
example : generatedDisplacementWidth (Equal.famA 3 0) = 6 := by decide
example : generatedDisplacementWidth (Equal.famB 3 0) = 5 := by decide
example : endpointWidth [] = 0 ∧ generatedDisplacementWidth [] = 1 := by decide
example : endpointWidth [0] = generatedDisplacementWidth [0] := by decide
example {r s m : Nat} (hr : 2 ≤ r) (hrs : r < s) : ¬ BoundedAt (s+1) (Unequal.family r s m) := by
  intro h
  have := (Unequal.family_boundedAt_iff hr hrs).mp h
  omega
example {r k : Nat} (hr : 3 ≤ r) : ¬ BoundedAt (r+2) (Equal.famA r k) := by
  intro h
  have := (Equal.famA_boundedAt_iff hr).mp h
  omega
example {r k : Nat} (hr : 3 ≤ r) : ¬ BoundedAt (r+1) (Equal.famB r k) := by
  intro h
  have := (Equal.famB_boundedAt_iff hr).mp h
  omega
#print axioms maxDisplacementFrom_bound
#print axioms endpointWidth_eq_displacement_of_pos
#print axioms Unequal.family_boundedAt_iff
#print axioms Equal.famA_boundedAt
#print axioms Equal.famA_boundedAt_iff
#print axioms Equal.famB_boundedAt_iff
#print axioms Unequal.family_minimal
#print axioms Equal.famA_minimal
#print axioms Equal.famB_minimal
end StackSorting.Generalized
