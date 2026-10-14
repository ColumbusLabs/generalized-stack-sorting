import AdhesionForests
import GuidanceIncidenceRealization
import MultiMarginEndpoint

/-!
Actual indexed routed paths give adhesion-only incidence guidance with a
fixed palette. This is the required 5.10-to-C.2 bridge; no outer bag capture
or global whole-bag guidance theorem is asserted.
-/
namespace StackSorting.GraphWidth.GeneralConstruction
open FinitePort Nested
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.IncidenceOwnership
open GuidedPathwidth GuidedPathwidth.IncidenceAdapter
variable {A : Model} {n t k : Nat} {G : Graph n} {T : RootedTree t}

/-- The original-edge rooted forests constructed by 5.10 transport to actual
incidence X/F/R sets, with the same parameter-only palette and root guards. -/
theorem routed_adhesions_incidence
    (D : Decomposition G T) (P : AdhesionGuidance.Paths D)
    (hb : P.Bounded k (2*k^3)) (hA : Laws A)
    (names : Fin n ≃ Vertex A)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val) :
    ∃ C : Colors A (4*k^3+2*k), C.Valid ∧
      CapturedLinkExtraction.MultiMargin.Captured D names C := by
  obtain ⟨F,hF⟩ := P.exists_paper_palette hb
  refine ⟨colors names F,colors_valid hA names hG F,?_⟩
  intro x hx
  have hx' : (AdhesionGuidance.adhesion D x).Nonempty := by
    obtain ⟨u,hu⟩ := hx
    exact ⟨u,(MultiMargin.adhesion_iff D x u).mpr hu⟩
  obtain ⟨z,hz⟩ := capture_to_incidence hA names hG F (hF x) hx'
  refine ⟨z,?_⟩
  intro u hu
  exact hz u ((MultiMargin.adhesion_iff D x u).mpr hu)

#print axioms routed_adhesions_incidence
end StackSorting.GraphWidth.GeneralConstruction
