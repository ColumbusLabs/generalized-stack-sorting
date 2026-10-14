import ContractedSaneDecomposition

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FinitePort
variable {n t : Nat} {G : Graph n} {T : RootedTree t}

/-- Joint actual construction: saneness, routed paths, low-pathwidth marginal
certificates and inherited adhesion containment all concern the SAME produced
decomposition. No downstream geometric certificate is assumed. -/
theorem exists_sane_supplied_low_pathwidth_parts (D : Decomposition G T)
    (connected : ∀ u v, GraphWidth.Walk G.Adj (fun _ => True) u v)
    (hn : 0 < n) (k : Nat) (width : D.BagBound (k+1)) :
    ∃ (m : Nat) (T' : RootedTree m) (E : Decomposition G T'),
      0<m ∧ MultiMargin.Sane E ∧
      (∃ P : AdhesionGuidance.Paths E, P.Bounded k (2*k^3)) ∧
      Nonempty (MarginalA2.Local.PathFamily E k) ∧
      (∀ i, ∃ x, ∀ v, AdhesionGuidance.adhesion E i v → v ∈ D.bag x) := by
  classical
  obtain ⟨r,hall,⟨S⟩⟩ := supplied_connected_routing D connected hn k width
  let O := (normalizeSupplied D).order
  have helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u :=
    normalized_eliminates G (introductionOrder D) (introductionEarlier_eliminates D)
  have hwidth : ∀ z, (regionBagSet G O z).card ≤ k+1 := by
    intro z
    rw [normalized_region_bag_eq]
    exact normalizeSupplied_bound D width z
  have downstream := solution_downstream S hall helim hwidth
  refine ⟨_,S.selected.selectedTree,S.selected.contractedDecomposition G hall helim,
    S.selected.selected_count_positive,?_,downstream.1,downstream.2,
    supplied_adhesion_containment D S.selected hall⟩
  exact S.selected.contracted_sane hall helim
    (normalized_cone_walks G (introductionOrder D))

#print axioms exists_sane_supplied_low_pathwidth_parts
end StackSorting.LowPathwidthParts
