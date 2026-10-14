import RootEmptyNumberedCodec
import FinitePortCodecRelabeling
import FiniteForestOrderRank

namespace StackSorting.GraphWidth
open FinitePort

/-- A normal code remembers its literal encoder, its exact original parent,
and the original chronology after temporary topological numbering. -/
structure NormalForestCodec {n colors relations : Nat}
    (G : Diagram n colors relations) (W : Nat)
    (P : Fin n → Fin n) (chronology : FixedOrder n)
    extends ExactRootEmptyCodec G W where
  order : FixedOrder n
  order_index : ∀ u, order.vertices.idxOf (index u) = chronology.vertices.idxOf u
  original_parent : ∀ i, label (tree.parent i) = P (label i)
  root_iff_fixed : ∀ i, i.val = 0 ↔ P (label i) = label i
  normal : code = encode tree order
    { color := fun i => G.color (label i), rel := fun q i j => G.rel q (label i) (label j) }

/-- No decomposition or numbered tree is supplied. A bounded connected
elimination forest produces a same-vertex normal code, preserving the
independent chronology rather than using numeric preorder as chronology. -/
theorem forest_has_normal_codec {n colors relations : Nat}
    (G : Diagram n colors relations) (H : Graph n)
    (hH : ∀ u v, H.Adj u v ↔ Adjacent G u v) (hl : Loopless G)
    (O : SameVertexForest.RankedOrder n)
    (he : ∀ u v, H.Adj u v →
      SameVertexForest.Ancestor O.forest u v ∨ SameVertexForest.Ancestor O.forest v u)
    {b : Nat} (hb : ∀ v, (eliminationFrontierSet O.forest H v).card ≤ b)
    (hc : ∀ u v, Walk H.Adj (fun _ => True) u v) (hn : 0 < n)
    (chronology : FixedOrder n) :
    Nonempty (NormalForestCodec G (b-1) O.parent chronology) := by
  obtain ⟨r,hr,ha,⟨N⟩⟩ := O.connected_numbered he hc hn
  let e : Fin n ≃ Fin n := ⟨N.index,N.label,N.label_index,N.index_label⟩
  let ord := CodecRelabeling.relabelOrder e chronology
  let G' := SameVertexForest.RankedOrder.Numbered.relabelDiagram O r hr ha N G
  have heG : ∀ u v, Adjacent G u v →
      SameVertexForest.Ancestor O.forest u v ∨ SameVertexForest.Ancestor O.forest v u :=
    fun u v h => he u v ((hH u v).mpr h)
  refine ⟨{ tree := N.tree
            label := N.label
            index := N.index
            label_index := N.label_index
            index_label := N.index_label
            code := encode N.tree ord G'
            bounded := ?_
            relation := ?_
            color := ?_
            root_ports := ?_
            order := ord
            order_index := ?_
            original_parent := N.parent_exact
            root_iff_fixed := ?_
            normal := rfl }⟩
  · exact SameVertexForest.RankedOrder.Numbered.bounded_codec O r hr ha N G H hH ord hb
  · exact SameVertexForest.RankedOrder.Numbered.decoded_original_relation O r hr ha N G ord hl heG
  · exact SameVertexForest.RankedOrder.Numbered.decoded_original_color O r hr ha N G ord
  · intro v hv
    simp only [encode,inherited_root_empty N.tree ord G' v hv,List.map_nil]
  · intro u
    exact CodecRelabeling.idxOf_map_equiv e chronology.vertices u
  · intro i
    constructor
    · intro hi
      rw [N.label_root i hi]
      exact hr
    · intro hi
      by_contra hnz
      have hpi : N.tree.parent i=i := N.label_injective ((N.parent_exact i).trans hi)
      have hlt := N.tree.parent_lt i hnz
      rw [hpi] at hlt
      exact Nat.lt_irrefl _ hlt

theorem NormalForestCodec.proper_parent_exact {n colors relations W : Nat}
    {G : Diagram n colors relations} {P : Fin n → Fin n} {O : FixedOrder n}
    (E : NormalForestCodec G W P O) (u v : Fin n) :
    (E.index v).val ≠ 0 ∧ E.tree.parent (E.index v)=E.index u ↔ P v=u ∧ u≠v := by
  constructor
  · rintro ⟨hz,hp⟩
    have hpar : P v=u := by
      have h := E.original_parent (E.index v)
      rw [hp,E.label_index,E.label_index] at h
      exact h.symm
    refine ⟨hpar,?_⟩
    intro he
    apply hz
    apply (E.root_iff_fixed _).mpr
    simpa only [E.label_index] using hpar.trans he
  · rintro ⟨hp,hn⟩
    constructor
    · intro hz
      have hfix := (E.root_iff_fixed _).mp hz
      rw [E.label_index,hp] at hfix
      exact hn hfix
    · apply Function.LeftInverse.injective E.index_label
      rw [E.original_parent,E.label_index,E.label_index]
      exact hp

#print axioms forest_has_normal_codec
#print axioms NormalForestCodec.proper_parent_exact
end StackSorting.GraphWidth
