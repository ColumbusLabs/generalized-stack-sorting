import MarginalLabelledUnary

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem labelled_adhesion (a b : F.LabelledCarrier) :
    F.labelledEval2 names hA hG C .adhesion a b ↔ (F.labelledRelations).adhesion a b := by
  rw [F.labelledEval2_formula]
  rcases a with v | (x | ⟨x, _ | u⟩) <;> rcases b with w | (y | ⟨y, _ | z⟩) <;>
    simp only [localCode,labelled_code_original,labelled_code_outer,labelled_code_some,labelled_code_none] <;>
    dsimp only [labelledRelations] <;>
    simp [NestedSyntax.atom] <;>
    simp [ActualEval,NestedSyntax.binary,NestedSyntax.pair,Actual.outputAtoms,outerAdhesion,Actual.Bag,Actual.Margin,Actual.outerAtoms,Actual.vertex,Actual.node,namedVertex]
  constructor
  · rintro ⟨⟨v,h,hv⟩,hn⟩
    have he : w=v := names.injective (Sum.inl.inj h)
    exact ⟨he.symm ▸ hv,hn w rfl⟩
  · rintro ⟨hw,hn⟩
    refine ⟨⟨w,rfl,hw⟩,?_⟩
    intro v h
    have he : w=v := names.injective (Sum.inl.inj h)
    exact he ▸ hn

#print axioms labelled_adhesion
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
