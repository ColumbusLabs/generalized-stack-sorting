import NumberedEliminationCodec

namespace StackSorting.GraphWidth
open FinitePort

/-- A concrete same-size finite-port code with exact decoding at a two-sided
renumbering. This record contains actual functions and a code, not an assumed
isomorphism between unrelated structures. -/
structure ExactNumberedCodec {n colors relations : Nat}
    (G : Diagram n colors relations) (W : Nat) where
  tree : RootedTree n
  label : Fin n → Fin n
  index : Fin n → Fin n
  label_index : ∀ u, label (index u) = u
  index_label : ∀ i, index (label i) = i
  code : Code n colors relations
  bounded : BoundedCode code W
  relation : ∀ q u v, DecodedRel tree code q (index u) (index v) ↔ G.rel q u v = true
  color : ∀ u c, (decode tree code).color (index u) c = G.color u c

/-- An actual supplied bounded decomposition of a connected nonempty graph
yields an actual bounded same-vertex code. No parent map, root, numbering
or code is assumed by this endpoint. The fixed order is only used for port order. -/
theorem decomposition_has_exact_codec {n t colors relations : Nat}
    (G : Diagram n colors relations) (H : Graph n)
    (hH : ∀ u v, H.Adj u v ↔ Adjacent G u v)
    (hl : Loopless G) {T : RootedTree t} (D : Decomposition H T)
    {b : Nat} (hb : D.BagBound b)
    (hc : ∀ u v, Walk H.Adj (fun _ => True) u v) (hn : 0 < n)
    (ord : FixedOrder n) : Nonempty (ExactNumberedCodec G (b-1)) := by
  let O := introductionOrder D
  have he : ∀ u v, H.Adj u v →
      SameVertexForest.Ancestor O.forest u v ∨ SameVertexForest.Ancestor O.forest v u :=
    fun _ _ h => eliminationForest_covers D h
  obtain ⟨r,hr,ha,hN⟩ := O.connected_numbered he hc hn
  obtain ⟨N⟩ := hN
  have heG : ∀ u v, Adjacent G u v →
      SameVertexForest.Ancestor O.forest u v ∨ SameVertexForest.Ancestor O.forest v u :=
    fun u v h => he u v ((hH u v).mpr h)
  let G' := SameVertexForest.RankedOrder.Numbered.relabelDiagram O r hr ha N G
  refine ⟨⟨N.tree, N.label, N.index, N.label_index, N.index_label,
    encode N.tree ord G', ?_, ?_, ?_⟩⟩
  · exact SameVertexForest.RankedOrder.Numbered.bounded_codec O r hr ha N G H hH ord
      (eliminationFrontier_bound D hb)
  · exact SameVertexForest.RankedOrder.Numbered.decoded_original_relation O r hr ha N G ord hl heG
  · exact SameVertexForest.RankedOrder.Numbered.decoded_original_color O r hr ha N G ord

#print axioms decomposition_has_exact_codec
end StackSorting.GraphWidth
