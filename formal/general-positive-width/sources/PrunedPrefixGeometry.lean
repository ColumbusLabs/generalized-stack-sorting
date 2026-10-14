import PrunedRegionBags

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

theorem pruned_clipped_parent (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) {v : Fin n} (hv : Cone O r v) :
    clippedParent (prunedOrder G O r s t) r v = clippedParent O r v := by
  by_cases he : v = r
  · simp [clippedParent,he]
  · have hrv : O.rel r v := hv.resolve_right (Ne.symm he)
    simp only [clippedParent,ite_eq_right he,pruned_parent G O cones r s t hrv]

/-- The pruning normalization preserves exactly the finite prefixes below the
original root, rather than assuming that an arbitrary reindexing preserves them. -/
theorem pruned_relativePrefix_iff (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) (Z : Finset (Fin n)) :
    RelativePrefix (prunedOrder G O r s t) r Z ↔ RelativePrefix O r Z := by
  constructor
  · intro h
    have hc : ∀ x ∈ Z, Cone O r x := fun x hx =>
      (pruned_cone_iff G O cones r s t (cone_refl O r)).mp (h.2.2 x hx)
    refine ⟨?_,h.2.1,hc⟩
    intro x hx
    rw [← pruned_clipped_parent G O cones r s t (hc x hx)]
    exact h.1 x hx
  · intro h
    refine ⟨?_,h.2.1,fun x hx => (pruned_cone_iff G O cones r s t (cone_refl O r)).mpr (h.2.2 x hx)⟩
    intro x hx
    rw [pruned_clipped_parent G O cones r s t (h.2.2 x hx)]
    exact h.1 x hx

theorem pruned_frontier_iff (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (z : Fin n) :
    Frontier (clippedParent (prunedOrder G O r s t) r) Z z ↔ Frontier (clippedParent O r) Z z := by
  have hp' := (pruned_relativePrefix_iff G O cones r s t Z).mpr hp
  constructor
  · intro hz
    have hc' := (relative_frontier_cone _ r Z hp' z hz).1
    have hc : O.rel r z := pruned_rel_old G O r s t hc'
    exact ⟨hz.1,(pruned_clipped_parent G O cones r s t (Or.inl hc)) ▸ hz.2⟩
  · intro hz
    have hc := (relative_frontier_cone O r Z hp z hz).1
    exact ⟨hz.1,(pruned_clipped_parent G O cones r s t (Or.inl hc)).symm ▸ hz.2⟩

end StackSorting.LowPathwidthParts
