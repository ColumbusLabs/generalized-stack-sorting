import MarginalLocalIncidenceFamily
import GenericCapturedWitness

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SameVertexForest ConnectedConeNormalization IndexTreeAdapter CapturedLinkExtraction
variable {n t k : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k)
variable (S : ∀ x, GenericIncidence.System (F.original x).simple)

/-- The concrete local guidance colors, on actual local incidence elements. -/
noncomputable def incidenceColors (x : Fin t) (i : Fin (BiInterface.PathWord.pathwidthPalette (2*k+2))) :
    (S x).ColorData := (S x).colorData ((F.guidance x).colors i)

/-- Normalized adhesions inherit capture from genuine local pathwidth guidance. -/
theorem incidence_adhesions_captured (x : Fin t) :
    (S x).AdhesionsCaptured (F.incidenceColors S x) (F.graph x)
      (normalizedOrder (F.graph x) (introductionOrder (F.localDecomposition x))) := by
  intro a ha
  have hcap := normalized_guided_adhesion_capture (F.guidance x) (F.numbering x) a
  have hc : ForestCaptures (F.guidance x).colors
      {u | RegionAdhesion (F.graph x)
        (normalizedOrder (F.graph x) (introductionOrder (F.localDecomposition x))) a u} := by
    exact hcap
  exact (S x).capture_to_incidence (F.guidance x).colors hc ha

/-- The whole fixed extraction tuple is constructed separately per owner.
Its arity includes the selected parent-link sets; it is not merely X/F/R. -/
theorem exists_local_extraction (x : Fin t) :
    ∃ X : Fin (CapturedLinkExtraction.parameterCount (BiInterface.PathWord.pathwidthPalette (2*k+2))) → (S x).IncSet,
      ∀ u v, ActualEval (S x).atoms
        (capturedEarlierFormula (fixedIndices (BiInterface.PathWord.pathwidthPalette (2*k+2))) (0 : Fin 2) 1)
        (Fin.cases (.inl u) (fun _ => .inl v)) X ↔ (F.normalized x).order.rel u v := by
  exact (S x).exists_earlier_of_captured_adhesions (F.incidenceColors S x)
    (F.incidence_colors_valid S x) (F.graph x) (fun _ _ => Iff.rfl)
    (introductionOrder (F.localDecomposition x)) (introductionEarlier_eliminates (F.localDecomposition x))
    (F.incidence_adhesions_captured S x)

noncomputable def extractionSets (x : Fin t) :
    Fin (CapturedLinkExtraction.parameterCount (BiInterface.PathWord.pathwidthPalette (2*k+2))) → (S x).IncSet :=
  Classical.choose (F.exists_local_extraction S x)

theorem extractionSets_exact (x : Fin t) (u v : Fin (F.vertices x)) :
    ActualEval (S x).atoms
      (capturedEarlierFormula (fixedIndices (BiInterface.PathWord.pathwidthPalette (2*k+2))) (0 : Fin 2) 1)
      (Fin.cases (.inl u) (fun _ => .inl v)) (F.extractionSets S x) ↔
        (F.normalized x).order.rel u v := Classical.choose_spec (F.exists_local_extraction S x) u v

#print axioms incidence_adhesions_captured
#print axioms exists_local_extraction
#print axioms extractionSets_exact
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
