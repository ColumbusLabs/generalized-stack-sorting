import MarginalMergedExtraction
import MarginalFiberFormula

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

/-- Local extracted order on the literal original-vertex codes. The only
existential owner in the syntax is forced to the actual unique outer owner. -/
theorem actualEarlier_same_owner (x : Fin t) (u v : Fin (F.vertices x)) :
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.earlier (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases (Incidence.embed D names x (F.names x) (.inl u))
        (fun _ => Incidence.embed D names x (F.names x) (.inl v)))
      (F.actualExtractionSets names hA hG C) ↔ (F.normalized x).order.rel u v := by
  let z := Incidence.embed D names x (F.names x) (.inl u)
  let w := Incidence.embed D names x (F.names x) (.inl v)
  let owner : Carrier.Actual (A := A) D := .inl (Actual.node x)
  let X := F.actualExtractionSets names hA hG C
  let env : Fin 3 → Carrier.Actual (A := A) D := Fin.cases owner (Fin.cases z (fun _ => w))
  have hz : Actual.outputAtoms D names .owner (Fin.cases z (fun _ => owner)) :=
    Incidence.embed_owned D names x (F.names x) (.inl u)
  have hw : Actual.outputAtoms D names .owner (Fin.cases w (fun _ => owner)) :=
    Incidence.embed_owned D names x (F.names x) (.inl v)
  have hp := Incidence.eval_project_local D names x (F.names x) hA hG C
    (capturedEarlierFormula (fixedIndices (BiInterface.PathWord.pathwidthPalette (2*k+2))) (0 : Fin 2) 1)
    (NestedSyntax.pair (1 : Fin 3) 2) 0 env (Fin.cases (.inl u) (fun _ => .inl v)) X
    (F.extractionSets (F.actualSystems names hA hG C) x) rfl
    (by intro i; fin_cases i <;> rfl)
    (fun j a => F.actualExtractionSets_restrict names hA hG C x j a)
  have hp' := hp.trans (F.extractionSets_exact (F.actualSystems names hA hG C) x u v)
  change (True ∧ True ∧ _) ↔ _
  rw [true_and,true_and]
  change (∃ o, Actual.outputAtoms D names .owner (Fin.cases z (fun _ => o)) ∧
    Actual.outputAtoms D names .owner (Fin.cases w (fun _ => o)) ∧
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.project (OwnerMerge.relativize
        (capturedEarlierFormula (fixedIndices (BiInterface.PathWord.pathwidthPalette (2*k+2))) (0 : Fin 2) 1)
        (NestedSyntax.pair (1 : Fin 3) 2) 0))
      (Fin.cases o (Fin.cases z (fun _ => w))) X) ↔ _
  constructor
  · rintro ⟨o,ho,_,h⟩
    have he := Actual.owner_functional D names ho hz
    subst o
    exact hp'.mp h
  · intro h
    exact ⟨owner,hz,hw,hp'.mpr h⟩

#print axioms actualEarlier_same_owner
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
