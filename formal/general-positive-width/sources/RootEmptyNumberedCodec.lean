import FiniteAlphabetBinaryCode

namespace StackSorting.GraphWidth
open FinitePort

/-- Root ports are empty in the actual constructed code. This extra fact is
needed to identify unbounded logical reachability with bounded readPort fuel. -/
structure ExactRootEmptyCodec {n colors relations : Nat}
    (G : Diagram n colors relations) (W : Nat) extends ExactNumberedCodec G W where
  root_ports : ∀ v, v.val = 0 → (code v).ports = []

theorem decomposition_has_rootEmpty_codec {n t colors relations : Nat}
    (G : Diagram n colors relations) (H : Graph n)
    (hH : ∀ u v, H.Adj u v ↔ Adjacent G u v)
    (hl : Loopless G) {T : RootedTree t} (D : Decomposition H T)
    {b : Nat} (hb : D.BagBound b)
    (hc : ∀ u v, Walk H.Adj (fun _ => True) u v) (hn : 0 < n)
    (ord : FixedOrder n) : Nonempty (ExactRootEmptyCodec G (b-1)) := by
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
  refine ⟨{ tree := N.tree
            label := N.label
            index := N.index
            label_index := N.label_index
            index_label := N.index_label
            code := encode N.tree ord G'
            bounded := ?_
            relation := ?_
            color := ?_
            root_ports := ?_ }⟩
  · exact SameVertexForest.RankedOrder.Numbered.bounded_codec O r hr ha N G H hH ord
      (eliminationFrontier_bound D hb)
  · exact SameVertexForest.RankedOrder.Numbered.decoded_original_relation O r hr ha N G ord hl heG
  · exact SameVertexForest.RankedOrder.Numbered.decoded_original_color O r hr ha N G ord
  · intro v hv
    simp only [encode,inherited_root_empty N.tree ord G' v hv,List.map_nil]

#print axioms decomposition_has_rootEmpty_codec
end StackSorting.GraphWidth
