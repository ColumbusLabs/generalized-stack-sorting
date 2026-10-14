import BoundedSubdivisionExtension
import ActualRectangleDecomposition

namespace StackSorting.GraphWidth.UCurve
open FinitePort PlaneGrid SubdivisionTree

/-- A bounded-radius source drawing has an actual decomposition with bags of
size at most 3*k. All planar, subdivision, spanning-tree, cotree, and projection
constructions are supplied by the drawing and its actual counted walks. -/
theorem source_decomposition_from_radius {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (k : Nat) (hk : 0<k)
    (radius : SourceApex.Radius (sourceGraph D) (endpointAnchor D) k) :
    ∃ t, ∃ T : RootedTree t, ∃ dec : Decomposition (sourceGraph D) T, dec.BagBound (3*k) := by
  let hw := rectangleWidth_positive events
  let hh := rectangleHeight_positive D
  obtain ⟨C,T,L,he,hbound⟩ := bounded_subdivision_extension (sourceGraph D) (endpointAnchor D)
    radius hk (TriRectangle.actualGraph hw hh) (TriRectangle.sourceApexRealization D)
    (TriRectangle.actualGraph_connected hw hh)
  have he' : ∀ i, i.val≠0 → (reindexGraph (TriRectangle.actualGraph hw hh) C).Adj i (T.parent i) :=
    fun i hi => (reindexGraph (TriRectangle.actualGraph hw hh) C).symm (he i hi)
  obtain ⟨dec,hdec⟩ := TriRectangle.exists_actual_lift_decomposition hw hh C T he' (sourceGraph D) L k hbound
  exact ⟨_,_,dec,hdec⟩

theorem source_decomposition_from_stems {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (k : Nat) (hk : 0<k)
    (hbound : ∀ e, (stemCrossings D e).length<k) :
    ∃ t, ∃ T : RootedTree t, ∃ dec : Decomposition (sourceGraph D) T, dec.BagBound (3*k) :=
  source_decomposition_from_radius D k hk (stems_give_apex_radius D k hbound)

/-- Original-machine generation supplies the geometry and source radius;
there is no assumed width, tree, plane embedding, or decomposition witness. -/
theorem generated_source_decomposition {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hrun : Generalized.Run r s [] (List.range n) output [])
    (hk : 0<max r s) :
    ∃ D : Drawing (canonicalPairing hp), ∃ t, ∃ T : RootedTree t,
      ∃ dec : Decomposition (sourceGraph D) T, dec.BagBound (3*max r s) := by
  obtain ⟨D,hD⟩ := generated_source_radius hp hrun
  have radius : SourceApex.Radius (sourceGraph D) (endpointAnchor D) (max r s) := by
    intro v
    obtain ⟨e,len,hl,hw⟩ := hD v
    exact ⟨anchor D e,len,⟨e,rfl⟩,hl,hw⟩
  obtain ⟨t,T,dec,hdec⟩ := source_decomposition_from_radius D (max r s) hk radius
  exact ⟨D,t,T,dec,hdec⟩

/-- The explicit source-label and endpoint lift multiplies 3*k by four. -/
theorem generated_sparse_decomposition {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hrun : Generalized.Run r s [] (List.range n) output [])
    (hk : 0<max r s) :
    ∃ t, ∃ T : RootedTree t,
      ∃ dec : Decomposition (sparseGraph (SparseEndpointMSO.canonicalDiagram output)
        (Generalized.canonicalEvents 0 output).length) T, dec.BagBound (12*max r s) := by
  obtain ⟨D,t,T,dec,hdec⟩ := generated_source_decomposition hp hrun hk
  obtain ⟨target,ht⟩ := explicit_source_decomposition_transfer hp D T dec (max r s) hdec
  exact ⟨t,T,target,ht⟩

/-- The central geometric width bound for an actually generated canonical
sparse endpoint graph. Positivity is explicit for the width subtraction. -/
theorem generated_sparse_treewidth {n r s : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hrun : Generalized.Run r s [] (List.range n) output [])
    (hk : 0<max r s) :
    HasTreewidthAtMost (sparseGraph (SparseEndpointMSO.canonicalDiagram output)
      (Generalized.canonicalEvents 0 output).length) (12*max r s-1) := by
  obtain ⟨t,T,dec,hdec⟩ := generated_sparse_decomposition hp hrun hk
  exact dec.treewidthAtMost hdec (by omega)

end StackSorting.GraphWidth.UCurve
