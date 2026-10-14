import MarginalIncidenceAtoms

namespace StackSorting.GraphWidth.MarginalA2.Actual
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open FinitePort Nested Incidence
variable {A : Model} {n t : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)

include hA hG in
theorem originalAdj_named (u v : Fin n) :
    OriginalAdj D names (vertex names u) (vertex names v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨hne,e,he,hu,hv⟩
    cases e with
    | inr e => exact he.elim
    | inl e => cases e with
      | inl e => exact he.elim
      | inr e =>
        have hg : G.Adj (originalLeft names e) (originalRight names e) := by
          apply (hG _ _).mpr
          simpa only [named_originalLeft,named_originalRight] using e.property.2
        have hu' := (original_incidence_named D names u e).mp hu
        have hv' := (original_incidence_named D names v e).mp hv
        rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
        · exact (hne (congrArg (vertex names) (hu'.trans hv'.symm))).elim
        · simpa only [hu',hv'] using hg
        · simpa only [hu',hv'] using G.symm hg
        · exact (hne (congrArg (vertex names) (hu'.trans hv'.symm))).elim
  · intro h
    have hn : u≠v := by intro he; subst v; exact G.loopless u h
    refine ⟨fun he => hn ((vertex_inj names).mp he),?_⟩
    obtain ⟨e,he | he⟩ := (edge_coverage hA _ _).mp ((hG u v).mp h)
    · exact ⟨.inl (.inr e),trivial,⟨trivial,Or.inl he.1.symm⟩,⟨trivial,Or.inr he.2.symm⟩⟩
    · exact ⟨.inl (.inr e),trivial,⟨trivial,Or.inr he.2.symm⟩,⟨trivial,Or.inl he.1.symm⟩⟩

#print axioms originalAdj_named
end StackSorting.GraphWidth.MarginalA2.Actual
