import MarginalLabelledUnary

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem labelled_originalEdge (a b : F.LabelledCarrier) :
    F.labelledEval2 names hA hG C .originalEdge a b ↔ (F.labelledRelations).originalEdge a b := by
  rw [F.labelledEval2_formula]
  rcases a with v | (x | ⟨x, _ | u⟩) <;> rcases b with w | (y | ⟨y, _ | z⟩) <;>
    simp only [localCode,labelled_code_original,labelled_code_outer,labelled_code_some,labelled_code_none] <;>
    dsimp only [labelledRelations] <;>
    simp [NestedSyntax.atom] <;>
    first
    | exact Actual.originalAdj_named D names hA hG v w
    | simp [ActualEval,NestedSyntax.binary,NestedSyntax.pair,Actual.outputAtoms,Actual.OriginalAdj,Actual.OriginalIncidence,Actual.OriginalEdge,Actual.outerAtoms,Actual.vertex,Actual.node,IsEdge,ElementIncident]

#print axioms labelled_originalEdge
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
