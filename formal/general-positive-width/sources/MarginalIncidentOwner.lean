import MarginalIncidenceAtoms

namespace StackSorting.GraphWidth.MarginalA2.Incidence
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open FinitePort Nested Actual
variable {A : Model} {n t q : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)
variable (x : Fin t) (localNames : Fin q ≃ {v : Fin n // introductionNode D v=x})

theorem oldEdgeOwner_node {e o : Carrier.Base A t} (h : OldEdgeOwner D names e o) :
    ∃ y : Fin t, o=Actual.node y := by
  obtain ⟨_,u,v,_,_,_,hu,_⟩ := h
  cases o with
  | inr y => exact ⟨y,rfl⟩
  | inl z => exact hu.elim

/-- Every marginal edge incident to a local vertex belongs to its actual
owner. Hence an unbounded ambient edge quantifier can safely be restricted
to the proved local incidence fiber. -/
theorem incident_owned (u : Fin q) (e : Carrier.Actual (A := A) D)
    (h : outputAtoms D names .incidence
      (Fin.cases (embed D names x localNames (.inl u)) (fun _ => e))) :
    outputAtoms D names .owner (Fin.cases e (fun _ => .inl (Actual.node x))) := by
  cases e with
  | inl e => cases e with
    | inr y => exact h.2.elim
    | inl e => cases e with
      | inl v =>
        exact (no_vertex_localEdge D names (names.symm v)
          (by simpa only [Actual.vertex,Equiv.apply_symm_apply] using h.1)).elim
      | inr e =>
        obtain ⟨o,ho⟩ := h.1
        obtain ⟨y,rfl⟩ := oldEdgeOwner_node D names ho
        have he := (original_owner_exact D names e y).mp ho
        have hi := (original_incidence_named D names (localNames u).val e).mp h.2
        have hy : y=x := by
          rcases hi with hi | hi
          · exact he.1.symm.trans (by simpa only [←hi] using (localNames u).property)
          · exact he.2.symm.trans (by simpa only [←hi] using (localNames u).property)
        subst y
        exact (original_actual_owner D names e x).mpr he
  | inr e =>
    have hi : (localNames u).val=e.val.1 ∨ (localNames u).val=e.val.2 := by
      exact h.elim (fun h => Or.inl ((Actual.vertex_inj names).mp h))
        (fun h => Or.inr ((Actual.vertex_inj names).mp h))
    have he : introductionNode D e.val.1=x := by
      rcases hi with hi | hi
      · simpa only [←hi] using (localNames u).property
      · exact (extra_same_owner D e).symm.trans (by simpa only [←hi] using (localNames u).property)
    exact embed_owned D names x localNames (.inr (.inr ⟨e,he⟩))

#print axioms incident_owned
end StackSorting.GraphWidth.MarginalA2.Incidence
