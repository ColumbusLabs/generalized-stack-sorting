import MarginalEarlierLocality
import MarginalEarlierValues

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem actualForestRoot (x : Fin t) (u : Fin (F.vertices x)) :
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.forestRoot (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 1))
      (fun _ => Incidence.embed D names x (F.names x) (.inl u))
      (F.actualExtractionSets names hA hG C) ↔ (F.normalized x).order.parent u=u := by
  classical
  let X := F.actualExtractionSets names hA hG C
  let code := Incidence.embed D names x (F.names x) (.inl u)
  have hex : (∃ z, ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.earlier (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases z (fun _ => code)) X) ↔ ∃ v, (F.normalized x).order.rel v u := by
    constructor
    · rintro ⟨z,hz⟩
      obtain ⟨v,_,hv⟩ := (F.earlier_into_local names hA hG C x u z).mp hz
      exact ⟨v,hv⟩
    · rintro ⟨v,hv⟩
      exact ⟨Incidence.embed D names x (F.names x) (.inl v),
        (F.actualEarlier_same_owner names hA hG C x v u).mpr hv⟩
  change (True ∧ ¬_) ↔ _
  rw [true_and]
  change (¬∃ z, ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.earlier (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases z (fun _ => code)) X) ↔ _
  rw [hex]
  constructor
  · intro hn
    by_contra hp
    exact hn ⟨_,(F.normalized x).order.parent_rel hp⟩
  · rintro hp ⟨v,hv⟩
    exact (F.normalized x).order.parent_ne_of_pred hv hp

#print axioms actualForestRoot
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
