import RootAdhesionPruning

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}
attribute [local instance] Classical.propDecidable

/-- Every globally renormalized pruned bag is contained in its old bag, so the
original width bound remains valid even at ambient isolated deleted vertices. -/
theorem pruned_bag_subset (G : Graph n) (O : RankedOrder n) (r s t v : Fin n) :
    regionBagSet (inducedGraph G (rootAllowed G O r s t)) (prunedOrder G O r s t) v ⊆
      regionBagSet G O v := by
  intro x hx
  apply (mem_regionBagSet G O v x).mpr
  rcases (mem_regionBagSet _ _ v x).mp hx with he | ⟨hxv,w,hw,hxw⟩
  · exact Or.inl he
  · exact Or.inr ⟨pruned_rel_old G O r s t hxv,w,
      ((normalized_cone _ O v w).mp hw).finish,hxw.1⟩

/-- Below the selected root, bags are exactly the original bags with the
unwanted root-adhesion vertices removed. No descendant reindexing is assumed. -/
theorem pruned_regionBag_iff (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) {v x : Fin n} (hv : Cone O r v) :
    RegionBag (inducedGraph G (rootAllowed G O r s t)) (prunedOrder G O r s t) v x ↔
      RegionBag G O v x ∧ rootAllowed G O r s t x := by
  constructor
  · intro h
    have hb := (mem_regionBagSet G O v x).mp
      (pruned_bag_subset G O r s t v ((mem_regionBagSet _ _ v x).mpr h))
    refine ⟨hb,?_⟩
    rcases h with he | ⟨_,w,_,hxw⟩
    · subst x
      exact cone_allowed G O r s t hv
    · exact hxw.2.1
  · rintro ⟨hb,keep⟩
    rcases hb with he | ⟨hxv,w,hw,hxw⟩
    · exact Or.inl he
    · have hkeepw := cone_allowed G O r s t (cone_trans O hv hw)
      have tail := (pruned_walk G O cones r s t hv hw).reverse
        (inducedGraph G (rootAllowed G O r s t)).symm
      have path : ReachCone (inducedGraph G (rootAllowed G O r s t)) O x v :=
        .step (cone_refl O x) ⟨hxw,keep,hkeepw⟩
          (tail.mono (fun y hy => cone_trans O (Or.inl hxv) hy))
      have hne : x ≠ v := by intro he; subst x; exact O.irrefl v hxv
      exact Or.inr ⟨⟨path,hne⟩,w,(pruned_cone_iff G O cones r s t hv).mpr hw,⟨hxw,keep,hkeepw⟩⟩

theorem pruned_bag_eq_filter (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) {v : Fin n} (hv : Cone O r v) :
    regionBagSet (inducedGraph G (rootAllowed G O r s t)) (prunedOrder G O r s t) v =
      (regionBagSet G O v).filter (rootAllowed G O r s t) := by
  classical
  ext x
  simp only [mem_regionBagSet,Finset.mem_filter,pruned_regionBag_iff G O cones r s t hv]

theorem pruned_adhesion_iff (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) {v x : Fin n} (hv : Cone O r v) :
    RegionAdhesion (inducedGraph G (rootAllowed G O r s t)) (prunedOrder G O r s t) v x ↔
      RegionAdhesion G O v x ∧ rootAllowed G O r s t x := by
  rw [regionAdhesion_iff,pruned_regionBag_iff G O cones r s t hv,regionAdhesion_iff]
  constructor
  · rintro ⟨⟨hb,hkeep⟩,hne⟩
    exact ⟨⟨hb,hne⟩,hkeep⟩
  · rintro ⟨⟨hb,hne⟩,hkeep⟩
    exact ⟨⟨hb,hkeep⟩,hne⟩

theorem pruned_width (G : Graph n) (O : RankedOrder n) (r s t : Fin n)
    (k : Nat) (width : ∀ v, (regionBagSet G O v).card ≤ k+1) :
    ∀ v, (regionBagSet (inducedGraph G (rootAllowed G O r s t))
      (prunedOrder G O r s t) v).card ≤ k+1 :=
  fun v => (Finset.card_le_card (pruned_bag_subset G O r s t v)).trans (width v)

end StackSorting.LowPathwidthParts
