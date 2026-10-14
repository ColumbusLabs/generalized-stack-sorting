import ConnectedRoutingExistence

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FinitePort
attribute [local instance] Classical.propDecidable
variable {n t : Nat} {G : Graph n} {T : RootedTree t}

/-- The actual supplied decomposition, rather than an assumed pathwidth
certificate, supplies the complete normalized root routing construction. -/
theorem supplied_connected_routing (D : Decomposition G T)
    (connected : ∀ u v, GraphWidth.Walk G.Adj (fun _ => True) u v)
    (hn : 0 < n) (k : Nat) (width : D.BagBound (k+1)) :
    ∃ r, (∀ v, Cone (normalizeSupplied D).order r v) ∧
      Nonempty (SubtreeRoutingSolution G (normalizeSupplied D).order r
        (emptyIncoming G (normalizeSupplied D).order r) k) := by
  apply exists_connected_routing G (normalizeSupplied D).order
    (normalized_eliminates G (introductionOrder D) (introductionEarlier_eliminates D))
    (normalized_cone_walks G (introductionOrder D)) connected hn k
  intro z
  rw [normalized_region_bag_eq]
  exact normalizeSupplied_bound D width z

/-- Every contracted adhesion is contained in the literal original supplied
bag at the retained introduction label. Unbounded contracted bags are never
used to justify the inherited finite adhesion palette. -/
theorem supplied_adhesion_containment (D : Decomposition G T)
    {r : Fin n} (A : RootedSelection (normalizeSupplied D).order r)
    (hall : ∀ v, Cone (normalizeSupplied D).order r v)
    (i : Fin (Fintype.card A.Selected)) :
    ∃ x, ∀ v, AdhesionGuidance.adhesion
      (A.contractedDecomposition G hall
        (normalized_eliminates G (introductionOrder D) (introductionEarlier_eliminates D))) i v →
      v ∈ D.bag x := by
  refine ⟨introductionNode D (A.selectedLabel i).val,?_⟩
  intro v hv
  apply normalizeSupplied_origin D
  rw [← normalized_region_bag_eq]
  apply (mem_regionBagSet G (normalizeSupplied D).order _ _).mpr
  exact ((A.actual_adhesion_iff G hall
    (normalized_eliminates G (introductionOrder D) (introductionEarlier_eliminates D)) i v).mp hv).2.1

end StackSorting.LowPathwidthParts
