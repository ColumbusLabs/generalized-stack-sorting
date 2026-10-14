import ContractedAdhesionGeometry

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization FinitePort
variable {n : Nat}

/-- Nonempty connected original graphs have one actual normalized root cone.
This is the only connectedness specialization needed by the Stack application. -/
theorem exists_covering_root (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (connected : ∀ u v, GraphWidth.Walk G.Adj (fun _ => True) u v)
    (hn : 0 < n) : ∃ r, O.parent r = r ∧ ∀ v, Cone O r v := by
  obtain ⟨r,hr,hall⟩ := O.connected_single_root
    (fun _ _ h => (helim h).elim (fun he => Or.inl (O.ancestor_of_rel he))
      (fun he => Or.inr (O.ancestor_of_rel he))) connected hn
  exact ⟨r,hr,fun v => O.ancestor_iff.mp (hall v)⟩

namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)
noncomputable local instance rootSpecDecidable : DecidablePred (fun x => x ∈ A.nodes) := Classical.decPred _

theorem selected_nonempty : Nonempty A.Selected := ⟨⟨r,A.root_mem⟩⟩

theorem selected_count_positive : 0 < Fintype.card A.Selected := by
  let : Nonempty A.Selected := A.selected_nonempty
  exact Fintype.card_pos

/-- All actual outer margins have explicitly exhibited original vertices. -/
theorem every_actual_margin_nonempty (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : Fin (Fintype.card A.Selected)) :
    (AdhesionGuidance.margin (A.contractedDecomposition G hall helim) i).Nonempty :=
  ⟨(A.selectedLabel i).val,A.actual_margin_representative G hall helim i⟩

end RootedSelection
end StackSorting.LowPathwidthParts
