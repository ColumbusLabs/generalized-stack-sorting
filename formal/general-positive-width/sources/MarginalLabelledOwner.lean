import MarginalLabelledUnary

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem labelled_owner (a b : F.LabelledCarrier) :
    F.labelledEval2 names hA hG C .owner a b ↔ (F.labelledRelations).owner a b := by
  rw [F.labelledEval2_formula]
  rcases a with v | (x | ⟨x, _ | u⟩) <;> rcases b with w | (y | ⟨y, _ | z⟩) <;>
    simp only [localCode,labelled_code_original,labelled_code_outer,labelled_code_some,labelled_code_none] <;>
    dsimp only [labelledRelations] <;>
    simp [NestedSyntax.atom] <;>
    simp [ActualEval,NestedSyntax.binary,NestedSyntax.pair,Actual.outputAtoms,Actual.OldOwner,Actual.OldEdgeOwner,Actual.OriginalEdge,Actual.Margin,Actual.outerAtoms,Actual.vertex,Actual.node,Incidence.embed,IsEdge]
  constructor
  · rintro ⟨v,h,hv⟩
    have he : (F.names x u).val=v := names.injective (Sum.inl.inj h)
    rw [←he,(F.names x u).property] at hv
    exact hv
  · intro h
    subst y
    exact ⟨(F.names x u).val,rfl,(F.names x u).property⟩

#print axioms labelled_owner
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
