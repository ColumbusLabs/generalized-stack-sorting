import MarginalLabelledAtoms
import MarginalNumberedAtoms

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (ht : 0<t) (hm : ∀ x, ∃ v, introductionNode D v=x)
variable (hc : ConnectedIntroductionComponents D)
variable (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

 theorem nested_code_factor
    (X : Fin (CapturedLinkExtraction.parameterCount (BiInterface.PathWord.pathwidthPalette (2*k+2))) →
      Carrier.Actual (A := A) D → Prop)
    (z : CarrierSemantics.Carrier (F.rootedNestedInput ht hm hc)) :
    F.nestedCodeEquiv ht hm hc names X z=
      F.labelledCodeEquiv names X (F.numberedLabelEquiv ht hm hc z) := by
  rcases z with v | (x | a) <;> rfl

theorem nested_encoded_atoms {r : Nat} (a : Nested.Syntax.InputAtom r)
    (env : Fin r → CarrierSemantics.Carrier (F.rootedNestedInput ht hm hc)) :
    stepAtoms (NestedSyntax.interpretation (BiInterface.PathWord.pathwidthPalette (2*k+2)))
      (Actual.outputAtoms D names) (F.actualExtractionSets names hA hG C) a
      (fun i => F.nestedCodeEquiv ht hm hc names (F.actualExtractionSets names hA hG C) (env i)) ↔
      Nested.Syntax.atoms (CarrierSemantics.relations (F.rootedNestedInput ht hm hc)) a env := by
  simp only [F.nested_code_factor ht hm hc names]
  exact (F.labelled_atoms names hA hG C a (fun i => F.numberedLabelEquiv ht hm hc (env i))).trans
    (F.numbered_atoms ht hm hc a env)

/-- Actual finite-copy nested realization, with fixed arity and no supplied
preorder, local incidence oracle, quotient, or nested representation premise. -/
noncomputable def nestedRealization {c d : Nat} {J : Parametric.Interpretation Syntax.OutputAtom c d}
    {params : Fin d → Nat → Prop}
    (R : Parametric.Realization J A params (Carrier.Actual (A := A) D) (Actual.outputAtoms D names)) :
    Parametric.Realization
      (Parametric.compose J (NestedSyntax.interpretation (BiInterface.PathWord.pathwidthPalette (2*k+2)))) A
      (Parametric.flattenedSets params (fun i => R.liftSet (F.actualExtractionSets names hA hG C i)))
      (CarrierSemantics.Carrier (F.rootedNestedInput ht hm hc))
      (Nested.Syntax.atoms (CarrierSemantics.relations (F.rootedNestedInput ht hm hc))) := by
  apply MultiMargin.Retained.transportRealization
    (R.compose (NestedSyntax.interpretation (BiInterface.PathWord.pathwidthPalette (2*k+2)))
      (F.actualExtractionSets names hA hG C))
    (F.nestedCodeEquiv ht hm hc names (F.actualExtractionSets names hA hG C)).symm
    (Nested.Syntax.atoms (CarrierSemantics.relations (F.rootedNestedInput ht hm hc)))
  intro r a env
  have h := F.nested_encoded_atoms ht hm hc names hA hG C a
    (fun i => (F.nestedCodeEquiv ht hm hc names (F.actualExtractionSets names hA hG C)).symm (env i))
  have he : (fun i => F.nestedCodeEquiv ht hm hc names (F.actualExtractionSets names hA hG C)
      ((F.nestedCodeEquiv ht hm hc names (F.actualExtractionSets names hA hG C)).symm (env i)))=env := by
    funext i
    exact (F.nestedCodeEquiv ht hm hc names (F.actualExtractionSets names hA hG C)).apply_symm_apply (env i)
  rw [he] at h
  exact h

 theorem nested_parameters_supported {c d : Nat} {J : Parametric.Interpretation Syntax.OutputAtom c d}
    {params : Fin d → Nat → Prop}
    (R : Parametric.Realization J A params (Carrier.Actual (A := A) D) (Actual.outputAtoms D names))
    (hp : CanonicalChoice.SupportedTuple A params) :
    CanonicalChoice.SupportedTuple A
      (Parametric.flattenedSets params (fun i => R.liftSet (F.actualExtractionSets names hA hG C i))) :=
  R.flattened_actual_supported hp (F.actualExtractionSets names hA hG C)

#print axioms nested_encoded_atoms
#print axioms nestedRealization
#print axioms nested_parameters_supported
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
