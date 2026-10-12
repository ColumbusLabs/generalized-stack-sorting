import CapacityBridge

/-! Kernel-checked boundary and non-vacuity checks; no native_decide. -/
namespace StackSorting.Labelled

example (H a : Nat) : RawFits H [.push0 a, .pop0] [] ↔ 1 ≤ H := by
  simp [RawFits, rawStep]

example : IsMinimumCapacity [] 0 0 := by
  refine ⟨⟨[], rfl, rfl, Nat.zero_le 0⟩, ?_⟩
  intro K _
  exact Nat.zero_le K

example : IsMinimumCapacity [1] 1 1 := by
  have hs : CanSort [] [1] (List.range' 1 1) :=
    ⟨[.push0 1, .pop0], rfl, rfl⟩
  simpa [maxDrop, maxDropFrom] using minimumCapacity_eq_maxDrop [1] 1 (by simp) hs

example : IsMinimumCapacity [2,1] 2 2 := by
  have hs : CanSort [] [2,1] (List.range' 1 2) :=
    ⟨[.push0 2, .push0 1, .pop0, .pop0], rfl, rfl⟩
  simpa [maxDrop, maxDropFrom] using minimumCapacity_eq_maxDrop [2,1] 2 (by simp) hs

example : ¬ CanSortWithin 0 [1] 1 := by
  intro h
  have hp := canSortWithin_positive 0 [1] 1 (by simp) h
  omega

example : ¬ Capacity.Fits 0 [.bypass] 0 := by
  simp [Capacity.Fits]

example : Capacity.Fits 1 [.bypass] 0 := by
  simp [Capacity.Fits]

#print axioms minimumCapacity_eq_maxDrop
#print axioms canonical_capacity_iff_fits
end StackSorting.Labelled
