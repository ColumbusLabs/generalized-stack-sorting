import CanonicalOuterPresentation
import NestedInheritedAdhesionBound
import MarginalPresentationEndpoint
import UniformNestedAdmissibility

/-!
Final assembly of the literal nested source witness using the checked A.2 endpoint.

The original source passed the independent final 607-module review on 2026-10-14.
This publication revision, dated 2026-10-14, changes only this header;
declarations and proofs are unchanged.
Original accepted source SHA-256: 564e217c4896efa138d8b5667e9e83f562a10fdccb6547089c9978056b84428b
-/
namespace StackSorting.GraphWidth.GeneralConstruction
open FinitePort Nested
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy SparseEndpointMSO.FiniteCopy.Parametric
open SparseEndpointMSO.IncidenceOwnership
open Nested.IntroductionSyntax

noncomputable def finalInterpretation (k : Nat) :=
  MarginalA2.presentation (outerInterpretation k) k (k+1)

noncomputable def finalVertexTag (k : Nat) :=
  MarginalA2.fullRetainedTag (k+1)
    (MultiMargin.ActualC2.physicalVertexTag (outerPalette k))

variable {A : Model} {n s k : Nat} {G : Graph n} {S : RootedTree s}
variable {D : Decomposition G S} {names : Fin n ≃ Vertex A} {hA : Laws A}
variable {hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val}

/-- Project the eight already-proved C.2 output atoms to the exact A.2 input
semantics. Representation, equality and original codes are unchanged. -/
def OuterPresentation.a2Realization (P : OuterPresentation D k names hA hG) :
    Parametric.Realization (outerInterpretation k) A P.params
      (MarginalA2.Carrier.Base A P.size) (MarginalA2.Actual.outerAtoms P.outer names) where
  rep := P.realization.rep
  valid := P.realization.valid
  cover := P.realization.cover
  complete := P.realization.complete
  equal := P.realization.equal
  atom a env actual hr := (P.realization.atom a env actual hr).trans
    (MarginalA2.Actual.outerAtoms_c2 P.outer names hA hG a actual).symm

/-- Every field of the literal nested source witness is now constructed from
one actual outer presentation. The fixed formula and tag depend only on k. -/
noncomputable def OuterPresentation.nestedWitness
    (P : OuterPresentation D k names hA hG) (width : D.BagBound (k+1))
    (hp : TimePath A n)
    (hraw : ∀ u v, G.Adj u v ↔ SparseEndpointMSO.EliminationSyntax.ModelAdjacent A u.val v.val)
    (hname : ∀ v, (names v).val=v.val) :
    NestedSourceWitness (finalInterpretation k) (finalVertexTag k)
      (k+1) (MarginalA2.localColors k) A := by
  let F := P.marginalPaths
  let hm : ∀ x, ∃ v, introductionNode P.outer v=x := P.sane.margin_nonempty
  let hc := P.sane.component_connected
  let N := F.rootedNestedInput P.nonempty hm hc
  let R := P.a2Realization
  refine {
    size := n
    graph := G
    treeSize := P.size
    tree := P.tree
    outer := P.outer
    nested := N
    adhesionBound := inherited_adhesionList_bound D P.outer N width P.containment
    localBound := F.rootedNestedInput_bound P.nonempty hm hc
    physicalTime := hp
    adjacency := hraw
    params := F.presentationSets names hA hG P.adhesionColoring R
    supported := F.presentation_supported names hA hG P.adhesionColoring R P.supported
    realization := F.presentationRealization P.nonempty hm hc names hA hG P.adhesionColoring R
    vertexCode := ?_ }
  intro v
  apply (F.presentation_original_rep P.nonempty hm hc names hA hG P.adhesionColoring R
    (MultiMargin.ActualC2.physicalVertexTag (outerPalette k)) v.val v).mpr
  change P.realization.rep
    (MultiMargin.ActualC2.physicalVertexTag (outerPalette k), v.val)
    (.inl (.inl (names v)))
  simpa only [hname v] using P.vertexCode v

/-- Actual canonical witnesses, including their fixed original vertex code,
are built from the original-machine run and the width-only bound. -/
theorem canonical_nested_witness {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n))
    (hr : Generalized.Run r s [] (List.range n) output [])
    (hne : (canonicalDiagram output).domain ≠ []) :
    Nonempty (NestedSourceWitness (finalInterpretation (12*max r s))
      (finalVertexTag (12*max r s)) (12*max r s+1)
      (MarginalA2.localColors (12*max r s)) (canonicalDiagram output)) := by
  obtain ⟨_,_,D,hb,⟨P⟩⟩ := canonical_outer_presentation hp hr hne
  exact ⟨P.nestedWitness hb (eventDiagram_path _)
    (CanonicalInput.event_sparseGraph_exact _) (fun _ => rfl)⟩

#print axioms canonical_nested_witness
end StackSorting.GraphWidth.GeneralConstruction
