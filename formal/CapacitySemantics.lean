import CapacityBridge
import CapacityComplete
import CountingSemantics

namespace StackSorting.Capacity
open StackSorting FirstReturn Labelled

/-- The exact grammar peak is the least physical capacity of its permutation,
using original no-bypass executions and the proved capacity-optimal canonical trace. -/
theorem path_capacity_iff (H : Nat) (p : Path) (hp : Valid p) :
    CanSortWithin H (permutation p) (pathWeight p) ↔ pathPeak p ≤ H := by
  obtain ⟨acts, c, he, hr, hi⟩ := decoded_trace (pathWeight p) (pathEncode p) (accepted_path p hp)
  have h := canonical_capacity_iff_fits H acts c (pathWeight p) hr
  rw [he, hi] at h
  exact h.trans (fits_path p H)

/-- Actual distinct inputs sortable with at most H physical storage positions. -/
abbrev BoundedInput (H n : Nat) := {input : List Nat // CanSortWithin H input n}

instance boundedInputFinite (H n : Nat) : Finite (BoundedInput H n) := by
  let f : BoundedInput H n → SortableInput n := fun input =>
    ⟨input.val, ((canSortWithin_iff_inputBound H input.val n).mp input.property).1⟩
  have hi : Function.Injective f := by
    intro input other h
    apply Subtype.ext
    exact congrArg (fun x : SortableInput n => x.val) h
  exact Finite.of_injective f hi

noncomputable instance (H n : Nat) : Fintype (BoundedInput H n) := Fintype.ofFinite _

def pathToBounded (H n : Nat) (p : PathSlice H n) : BoundedInput H n :=
  ⟨permutation p.val.val, by
    have h := (path_capacity_iff H p.val.val p.property.1).mpr p.property.2
    simpa [p.val.property] using h⟩

theorem pathToBounded_bijective (H n : Nat) : Function.Bijective (pathToBounded H n) := by
  constructor
  · intro p q h
    apply Subtype.ext
    apply Subtype.ext
    apply permutation_injective _ _ p.property.1 q.property.1
    · exact p.val.property.trans q.val.property.symm
    · exact congrArg Subtype.val h
  · intro input
    have hs := ((canSortWithin_iff_inputBound H input.val n).mp input.property).1
    obtain ⟨p, hp, hw, he⟩ := permutation_surjective n input.val hs
    have hc : CanSortWithin H (permutation p) (pathWeight p) := by
      simpa [he, hw] using input.property
    have hh := (path_capacity_iff H p hp).mp hc
    exact ⟨⟨⟨p, hw⟩, hp, hh⟩, Subtype.ext he⟩

noncomputable def grammarBoundedEquiv (H n : Nat) : PathSlice H n ≃ BoundedInput H n :=
  Equiv.ofBijective (pathToBounded H n) (pathToBounded_bijective H n)

theorem pathCount_eq_bounded_card (H n : Nat) :
    pathCount H n = Fintype.card (BoundedInput H n) :=
  Fintype.card_congr (grammarBoundedEquiv H n)

noncomputable def capacitySeries (H : Nat) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Fintype.card (BoundedInput H n) : ℤ)

theorem capacitySeries_eq_pathSeries (H : Nat) : capacitySeries H = pathSeries H := by
  ext n
  simp [capacitySeries, pathSeries, pathCount_eq_bounded_card]

theorem capacitySeries_coeff (H n : Nat) :
    PowerSeries.coeff n (capacitySeries H) = (Fintype.card (BoundedInput H n) : ℤ) := by
  simp [capacitySeries]

#print axioms path_capacity_iff
#print axioms pathToBounded_bijective
#print axioms capacitySeries_eq_pathSeries
end StackSorting.Capacity
