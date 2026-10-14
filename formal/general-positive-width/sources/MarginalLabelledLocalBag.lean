import MarginalLabelledUnary

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem labelled_localBag (a b : F.LabelledCarrier) :
    F.labelledEval2 names hA hG C .localBag a b ↔ (F.labelledRelations).localBag a b := by
  rw [F.labelledEval2_formula]
  rcases a with v | (x | ⟨x, _ | u⟩) <;> rcases b with w | (y | ⟨y, _ | z⟩) <;>
    simp only [localCode,labelled_code_original,labelled_code_outer,labelled_code_some,labelled_code_none] <;>
    dsimp only [labelledRelations] <;>
    simp [NestedSyntax.atom]
  all_goals first
    | change ¬¬True; exact fun h => h trivial
    | change ¬(False ∧ _); exact fun h => h.1
    | change (True ∧ _) ↔ _
      rw [true_and]
      exact F.actualLocalBag_global names hA hG C x u w

#print axioms labelled_localBag
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
