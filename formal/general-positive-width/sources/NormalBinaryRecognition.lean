import NormalForestCodec
import BuiltBinaryOrder
import BinaryCodePortDecoder

namespace StackSorting.GraphWidth.NormalForestCodec
open FinitePort FinitePort.ChildSibling TreeAutomaton.Logic
open FinitePort.ChildSibling.BinaryOrderMSO
variable {n colors relations W : Nat} {G : Diagram n colors relations}
  {P : Fin n → Fin n} {O : FixedOrder n} (E : NormalForestCodec G W P O)

def numberedDiagram : Diagram n colors relations where
  color i := G.color (E.label i)
  rel q i j := G.rel q (E.label i) (E.label j)

theorem normal_numbered : E.code=encode E.tree E.order E.numberedDiagram := E.normal

theorem order_label (i : Fin n) :
    E.order.vertices.idxOf i=O.vertices.idxOf (E.label i) := by
  simpa only [E.index_label] using E.order_index (E.label i)

theorem binaryCode_selected_parent (hn : 0<n)
    (p q : Position (binaryCode E.toExactNumberedCodec E.order hn)) :
    ParentPosition p q ↔
      P (binaryCodeVertexEquiv E.toExactNumberedCodec E.order hn q)=
        binaryCodeVertexEquiv E.toExactNumberedCodec E.order hn p ∧
      binaryCodeVertexEquiv E.toExactNumberedCodec E.order hn p≠
        binaryCodeVertexEquiv E.toExactNumberedCodec E.order hn q := by
  rw [binaryCode_parent]
  have h := E.proper_parent_exact
    (E.label (binaryCodeIndexEquiv E.toExactNumberedCodec E.order hn p))
    (E.label (binaryCodeIndexEquiv E.toExactNumberedCodec E.order hn q))
  simpa only [E.index_label,binaryCodeVertexEquiv,Equiv.trans_apply,Equiv.coe_fn_mk] using h

/-- The constructed normal encoder satisfies the complete literal port/shape/
sibling sentence. The order hypothesis is on the original chronology; temporary
numbering is transported by the codec's proved index laws. -/
theorem binaryCode_exact_sentence (hn : 0<n)
    (order : Formula (Alphabet colors relations W) 2)
    (ho : ExactPositionOrder O (binaryCode E.toExactNumberedCodec E.order hn)
      (binaryCodeVertexEquiv E.toExactNumberedCodec E.order hn) order) :
    (exactCodeSentence order (fun q => relationRoute parentRoute q)).EvalAt
      (binaryCode E.toExactNumberedCodec E.order hn) Fin.elim0 := by
  let C := E.toExactNumberedCodec
  let t := binaryCode C E.order hn
  let e := binaryCodeIndexEquiv C E.order hn
  have horder : ExactPositionOrder E.order t e order := by
    intro p q
    rw [ho]
    change O.vertices.idxOf (E.label (e p)) < O.vertices.idxOf (E.label (e q)) ↔
      E.order.vertices.idxOf (e p) < E.order.vertices.idxOf (e q)
    rw [E.order_label,E.order_label]
  have hrel : ∀ q p p', (relationRoute parentRoute q).EvalAt t (SparseTreeCompiler.binaryVal p p') ↔
      E.numberedDiagram.rel q (e p) (e p')=true := by
    intro q p p'
    exact binaryCode_relationRoute E.toExactRootEmptyCodec E.order hn q p p'
  have hcolor : ∀ p : Position t, p.label.toLabel.color=E.numberedDiagram.color (e p) := by
    intro p
    funext c
    exact binaryCode_original_color C E.order hn p c
  apply (exactCodeSentence_correct E.tree E.order E.numberedDiagram t e order _
    (binaryCode_parent C E.order hn) horder hrel hcolor).mpr
  refine ⟨binaryCode_normalized C E.order hn,binaryCode_sibling_strict C E.order hn,?_⟩
  calc
    labelCode (indexedLabels t e)=E.code := by
      funext i
      change (e.symm i).label.toLabel=E.code i
      simpa only [e,C,Equiv.apply_symm_apply] using binaryCode_label C E.order hn (e.symm i)
    _ = encode E.tree E.order E.numberedDiagram := E.normal_numbered

#print axioms binaryCode_selected_parent
#print axioms binaryCode_exact_sentence
end StackSorting.GraphWidth.NormalForestCodec
