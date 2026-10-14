import MarginalLabelledUnary
import MarginalRootValues

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem labelled_localParent (a b : F.LabelledCarrier) :
    F.labelledEval2 names hA hG C .localParent a b ↔ (F.labelledRelations).localParent a b := by
  rw [F.labelledEval2_formula]
  rcases a with v | (x | ⟨x, _ | u⟩) <;> rcases b with w | (y | ⟨y, _ | z⟩) <;>
    simp only [localCode,labelled_code_original,labelled_code_outer,labelled_code_some,labelled_code_none] <;>
    dsimp only [labelledRelations] <;>
    simp [NestedSyntax.atom]
  all_goals first
    | change ¬¬True; exact fun h => h trivial
    | simpa only [Sigma.mk.injEq] using F.forestParent_labels names hA hG C x y u z
    | change (ActualEval (Actual.outputAtoms D names)
        (NestedSyntax.forestRoot (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2)) _ _ ∧
        ActualEval (Actual.outputAtoms D names) (NestedSyntax.binary .owner (0 : Fin 2) 1) _ _) ↔ _
      rw [NestedSyntax.eval_forestRoot_values,NestedSyntax.eval_binary_values]
      have h := F.forestRoot_parent_labels names hA hG C x y u
      simp only [Sigma.mk.injEq] at h
      convert h using 1; rfl

#print axioms labelled_localParent
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
