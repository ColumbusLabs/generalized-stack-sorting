import CapacitySemantics

namespace StackSorting.Capacity
open StackSorting FirstReturn PowerSeries

theorem treeExtra_le_weight (t : Tree) : treeExtra t ≤ weight t := by
  induction t <;> simp_all [treeExtra, weight] <;> omega

theorem pathPeak_le_weight (p : Path) : pathPeak p ≤ pathWeight p := by
  induction p with
  | nil => simp [pathPeak, pathWeight]
  | bypass p ih => simp only [pathPeak, pathWeight]; omega
  | push t p ih =>
      have ht := treeExtra_le_weight t
      simp only [pathPeak, pathWeight]; omega

def stabilizedEquiv (H n : Nat) (hn : n ≤ H) :
    PathSlice H n ≃ FirstReturn.PathSlice n where
  toFun p := ⟨p.val, p.property.1⟩
  invFun p := ⟨p.val, p.property, by
    have hh := pathPeak_le_weight p.val.val
    rw [p.val.property] at hh
    exact hh.trans hn⟩
  left_inv p := rfl
  right_inv p := rfl

theorem pathCount_stabilizes (H n : Nat) (hn : n ≤ H) :
    pathCount H n = FirstReturn.pathCount n :=
  Fintype.card_congr (stabilizedEquiv H n hn)

/-- At every fixed degree n, physical capacity n already gives the unbounded
original-permutation coefficient. This is exact coefficientwise stabilization. -/
theorem capacitySeries_stabilizes (H n : Nat) (hn : n ≤ H) :
    coeff n (capacitySeries H) = coeff n sortingSeries := by
  rw [capacitySeries_eq_pathSeries, sortingSeries_eq_pathSeries]
  simp only [coeff_pathSeries, FirstReturn.coeff_pathSeries]
  rw [pathCount_stabilizes H n hn]

theorem pathCount_mono (H K n : Nat) (hHK : H ≤ K) : pathCount H n ≤ pathCount K n := by
  let f : PathSlice H n → PathSlice K n := fun p =>
    ⟨p.val, p.property.1, p.property.2.trans hHK⟩
  have hi : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun x : PathSlice K n => x.val) h
  exact Fintype.card_le_of_injective f hi

#print axioms capacitySeries_stabilizes
#print axioms pathCount_mono
end StackSorting.Capacity
