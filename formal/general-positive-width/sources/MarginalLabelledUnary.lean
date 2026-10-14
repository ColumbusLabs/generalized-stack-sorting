import MarginalLabelledEval

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem labelled_unary_generic
    (X : Fin (CapturedLinkExtraction.parameterCount (BiInterface.PathWord.pathwidthPalette (2*k+2))) →
      Carrier.Actual (A := A) D → Prop)
    (atom : Nested.Syntax.InputAtom 1) (z : F.LabelledCarrier) :
    stepAtoms (NestedSyntax.interpretation (BiInterface.PathWord.pathwidthPalette (2*k+2)))
      (Actual.outputAtoms D names) X atom (fun _ => F.labelledCodeEquiv names X z) ↔
      Nested.Syntax.atoms F.labelledRelations atom (fun _ => z) := by
  cases atom <;> rcases z with v | (x | ⟨x, _ | u⟩) <;>
    simp only [stepAtoms,NestedSyntax.interpretation,
      labelled_code_original,labelled_code_outer,labelled_code_some,labelled_code_none] <;>
    first
    | change True ↔ True; exact Iff.rfl
    | change False ↔ False; exact Iff.rfl
    | change (¬True) ↔ False; exact ⟨fun h => h trivial,fun h => h.elim⟩
    | change True ↔ _; exact ⟨fun _ => rfl,fun _ => trivial⟩
    | change (¬True) ↔ _; constructor; intro h; exact (h trivial).elim; intro h; cases h

theorem labelled_unary (atom : Nested.Syntax.InputAtom 1) (z : F.LabelledCarrier) :
    F.labelledEval1 names hA hG C atom z ↔ Nested.Syntax.atoms F.labelledRelations atom (fun _ => z) :=
  F.labelled_unary_generic names (F.actualExtractionSets names hA hG C) atom z

#print axioms labelled_unary
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
