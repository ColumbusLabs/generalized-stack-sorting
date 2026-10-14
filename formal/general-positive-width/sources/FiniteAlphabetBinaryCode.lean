import BinaryPositionRelabeling
import BinaryShapeParent
import FinitePortAlphabet

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic GraphWidth

@[simp] theorem map_numNodes {α β : Type} (f : α → β) (t : BinaryTree α) :
    (t.map f).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp only [BinaryTree.map, BinaryTree.numNodes, hl, hr]

/-- The temporary distinct vertex names are erased; the stored labels belong
only to the width- and vocabulary-dependent finite alphabet. -/
noncomputable def binaryCode {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n) :
    BinaryTree (Alphabet colors relations W) :=
  (build E.tree O n [⟨0,hn⟩]).map (alphabetCode E.code E.bounded)

theorem binaryCode_numNodes {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n) :
    (binaryCode E O hn).numNodes = n := by
  rw [binaryCode, map_numNodes]
  exact root_shape_numNodes E.tree O ⟨0,hn⟩ rfl

/-- Shape addresses still name every numbered vertex exactly once after the
possibly noninjective finite-alphabet relabelling. -/
noncomputable def binaryCodeIndexEquiv {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n) :
    Position (binaryCode E O hn) ≃ Fin n :=
  (positionMapEquiv (alphabetCode E.code E.bounded) (build E.tree O n [⟨0,hn⟩])).symm.trans
    (shapePositionEquiv E.tree O ⟨0,hn⟩ rfl)

/-- Compose the exact address numbering with the original graph's naming. -/
noncomputable def binaryCodeVertexEquiv {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n) :
    Position (binaryCode E O hn) ≃ Fin n :=
  (binaryCodeIndexEquiv E O hn).trans
    ⟨E.label,E.index,E.index_label,E.label_index⟩

theorem binaryCode_label {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (p : Position (binaryCode E O hn)) :
    p.label.toLabel = E.code (binaryCodeIndexEquiv E O hn p) := by
  change p.label.toLabel = E.code
    (unmapPosition (alphabetCode E.code E.bounded) (build E.tree O n [⟨0,hn⟩]) p).label
  have hh := unmapPosition_label (alphabetCode E.code E.bounded)
    (build E.tree O n [⟨0,hn⟩]) p
  exact (congrArg Alphabet.toLabel hh).symm.trans (Alphabet.toLabel_ofLabel ..)

/-- Pointwise transport of the already checked abstract-port decoding. The
uniform MSO route formula on binary positions is a separate subsequent join. -/
theorem binaryCode_original_relation {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (q : Fin relations) (p p' : Position (binaryCode E O hn)) :
    DecodedRel E.tree E.code q (binaryCodeIndexEquiv E O hn p)
      (binaryCodeIndexEquiv E O hn p') ↔
      G.rel q (binaryCodeVertexEquiv E O hn p) (binaryCodeVertexEquiv E O hn p') = true := by
  simpa only [binaryCodeVertexEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, E.index_label] using
    E.relation q (E.label (binaryCodeIndexEquiv E O hn p))
      (E.label (binaryCodeIndexEquiv E O hn p'))

theorem binaryCode_original_color {n colors relations W} {G : Diagram n colors relations}
    (E : ExactNumberedCodec G W) (O : FixedOrder n) (hn : 0 < n)
    (p : Position (binaryCode E O hn)) (c : Fin colors) :
    p.label.toLabel.color c = G.color (binaryCodeVertexEquiv E O hn p) c := by
  rw [binaryCode_label]
  simpa only [decode, binaryCodeVertexEquiv, Equiv.trans_apply, Equiv.coe_fn_mk,
    E.index_label] using E.color (E.label (binaryCodeIndexEquiv E O hn p)) c

#print axioms binaryCode_numNodes
#print axioms binaryCodeVertexEquiv
#print axioms binaryCode_original_relation
end StackSorting.FinitePort.ChildSibling
