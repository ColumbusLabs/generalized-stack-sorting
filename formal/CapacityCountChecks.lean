import CapacitySemantics
namespace StackSorting.Capacity
open StackSorting FirstReturn Mark PowerSeries
example : pathPeak (.bypass .nil) = 1 := rfl
example : ¬ Fits 0 (pathEncode (.bypass .nil)) 0 := by simp [pathEncode, Fits]
example : Fits 1 (pathEncode (.bypass (.bypass .nil))) 0 := by simp [pathEncode, Fits]
example (h : Nat) : count h 0 L (some L) true (some L) = 2 := by simp [count_zero, eval]
example (h : Nat) : count h 0 R (some L) false (some L) = 0 := by simp
example (n : Nat) : count 0 (n+1) L none true none = 0 := count_no_space n L none none true
example : series 0 L (some L) true (some L) = 2 := by
  rw [series_no_space]
  simp [count_zero, eval]
example : capacitySeries 0 = 1 := by rw [capacitySeries_eq_pathSeries, pathSeries_no_space]
example : Fintype.card (BoundedInput 0 1) = 0 := by
  rw [← pathCount_eq_bounded_card]
  exact pathCount_no_space 0
example : ¬ Valid (.push .pop0 .nil) := by simp [Valid, eval]
example (h : Nat) : constantCoeff (capacitySeries h) = 1 := by
  rw [capacitySeries_eq_pathSeries]
  exact constantCoeff_pathSeries h
#print axioms pathCount_eq_bounded_card
#print axioms capacitySeries_coeff
end StackSorting.Capacity
