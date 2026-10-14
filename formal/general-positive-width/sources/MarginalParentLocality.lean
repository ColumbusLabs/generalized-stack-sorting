import MarginalLocalParentSemantics

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem actualForestParent_any (x : Fin t) (v : Fin (F.vertices x)) (z : Carrier.Actual (A := A) D) :
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.forestParent (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases (Incidence.embed D names x (F.names x) (.inl v)) (fun _ => z))
      (F.actualExtractionSets names hA hG C) ↔
      ∃ u, z=Incidence.embed D names x (F.names x) (.inl u) ∧ (F.normalized x).order.Cover u v := by
  constructor
  · intro h
    have hr := (NestedSyntax.eval_earlier_values (Actual.outputAtoms D names) (1 : Fin 2) 0
      (Fin.cases (Incidence.embed D names x (F.names x) (.inl v)) (fun _ => z))
      (F.actualExtractionSets names hA hG C)).mp h.1
    obtain ⟨u,hu,_⟩ := (F.earlier_into_local names hA hG C x v z).mp hr
    subst z
    exact ⟨u,rfl,(F.actualForestParent_cover names hA hG C x v u).mp h⟩
  · rintro ⟨u,rfl,h⟩
    exact (F.actualForestParent_cover names hA hG C x v u).mpr h

#print axioms actualForestParent_any
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
