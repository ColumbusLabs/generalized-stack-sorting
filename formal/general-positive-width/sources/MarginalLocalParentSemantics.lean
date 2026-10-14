import MarginalLocalRootSemantics

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem actualForestParent_cover (x : Fin t) (child parent : Fin (F.vertices x)) :
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.forestParent (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases (Incidence.embed D names x (F.names x) (.inl child))
        (fun _ => Incidence.embed D names x (F.names x) (.inl parent)))
      (F.actualExtractionSets names hA hG C) ↔ (F.normalized x).order.Cover parent child := by
  let code := fun u => Incidence.embed D names x (F.names x) (.inl u)
  let X := F.actualExtractionSets names hA hG C
  let env : Fin 2 → Carrier.Actual (A := A) D := Fin.cases (code child) (fun _ => code parent)
  let colors := BiInterface.PathWord.pathwidthPalette (2*k+2)
  have hfirst : ActualEval (Actual.outputAtoms D names) (NestedSyntax.earlier colors 1 0) env X ↔
      (F.normalized x).order.rel parent child :=
    (NestedSyntax.eval_earlier_values (Actual.outputAtoms D names) 1 0 env X).trans
      (F.actualEarlier_same_owner names hA hG C x parent child)
  have hmiddle : (∃ z, ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.earlier colors (2 : Fin 3) 0) (Fin.cases z env) X ∧
      ActualEval (Actual.outputAtoms D names)
        (NestedSyntax.earlier colors (0 : Fin 3) 1) (Fin.cases z env) X) ↔
      ∃ v, (F.normalized x).order.rel parent v ∧ (F.normalized x).order.rel v child := by
    constructor
    · rintro ⟨z,hp,hc⟩
      have hp' := (NestedSyntax.eval_earlier_values (Actual.outputAtoms D names) 2 0 (Fin.cases z env) X).mp hp
      have hc' := (NestedSyntax.eval_earlier_values (Actual.outputAtoms D names) 0 1 (Fin.cases z env) X).mp hc
      obtain ⟨v,hv,hvc⟩ := (F.earlier_into_local names hA hG C x child z).mp hc'
      subst z
      exact ⟨v,(F.actualEarlier_same_owner names hA hG C x parent v).mp hp',hvc⟩
    · rintro ⟨v,hpv,hvc⟩
      refine ⟨code v,?_,?_⟩
      · apply (NestedSyntax.eval_earlier_values (Actual.outputAtoms D names) 2 0 (Fin.cases (code v) env) X).mpr
        exact (F.actualEarlier_same_owner names hA hG C x parent v).mpr hpv
      · apply (NestedSyntax.eval_earlier_values (Actual.outputAtoms D names) 0 1 (Fin.cases (code v) env) X).mpr
        exact (F.actualEarlier_same_owner names hA hG C x v child).mpr hvc
  change (ActualEval (Actual.outputAtoms D names) (NestedSyntax.earlier colors 1 0) env X ∧
      ¬∃ z, ActualEval (Actual.outputAtoms D names) (NestedSyntax.earlier colors (2 : Fin 3) 0) (Fin.cases z env) X ∧
        ActualEval (Actual.outputAtoms D names) (NestedSyntax.earlier colors (0 : Fin 3) 1) (Fin.cases z env) X) ↔ _
  rw [hfirst,hmiddle]
  rfl

#print axioms actualForestParent_cover
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
