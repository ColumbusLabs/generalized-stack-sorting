import BinaryGraphCodeUniqueness
import BinaryOrderMSOSyntax

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic SparseTreeCompiler BinaryOrderMSO

/-- One literal sentence checks normalized binary shape, chronological sibling
order, and every exact finite-port entry. It does not select a decomposition. -/
noncomputable def exactCodeSentence {colors relations W}
    (order : Formula (Alphabet colors relations W) 2)
    (rel : Fin relations → Formula (Alphabet colors relations W) 2) :
    Formula (Alphabet colors relations W) 0 :=
  .conj (normalizedOrderedSentence order) (normalSlotsFormula parentRoute order rel)

theorem exactCodeSentence_correct {n colors relations W}
    (T : RootedTree n) (O : FixedOrder n) (G : Diagram n colors relations)
    (t : BinaryTree (Alphabet colors relations W)) (e : Position t ≃ Fin n)
    (order : Formula (Alphabet colors relations W) 2)
    (rel : Fin relations → Formula (Alphabet colors relations W) 2)
    (hp : ∀ p q, ParentPosition p q ↔ (e q).val≠0 ∧ T.parent (e q)=e p)
    (ho : ExactPositionOrder O t e order)
    (hr : ∀ s p q, (rel s).EvalAt t (binaryVal p q) ↔ G.rel s (e p) (e q)=true)
    (hc : ∀ p : Position t, p.label.toLabel.color=G.color (e p)) :
    (exactCodeSentence order rel).EvalAt t Fin.elim0 ↔
      NormalizedBinaryShape t ∧ SiblingOrderStrict O t e ∧
        labelCode (indexedLabels t e)=encode T O G := by
  change ((normalizedOrderedSentence order).EvalAt t Fin.elim0 ∧
    (normalSlotsFormula parentRoute order rel).EvalAt t Fin.elim0) ↔ _
  rw [evalAt_normalizedOrderedSentence O t e order ho,
    indexed_normalSlots_correct T O G t e order rel hp ho hr hc,and_assoc]

/-- Exact sentence membership, rather than an assumed equality of child lists
or labels, forces literal tree equality for fixed original parent and order. -/
theorem exact_sentence_graph_code_unique {n colors relations W}
    (T : RootedTree n) (O : FixedOrder n) (G : Diagram n colors relations)
    (a b : Alphabet colors relations W) (l r : BinaryTree (Alphabet colors relations W))
    (e : Position (.node a l .nil) ≃ Fin n) (f : Position (.node b r .nil) ≃ Fin n)
    (order : Formula (Alphabet colors relations W) 2)
    (rel : Fin relations → Formula (Alphabet colors relations W) 2)
    (he : ∀ p q, ParentPosition p q ↔ (e q).val≠0 ∧ T.parent (e q)=e p)
    (hf : ∀ p q, ParentPosition p q ↔ (f q).val≠0 ∧ T.parent (f q)=f p)
    (hoe : ExactPositionOrder O (.node a l .nil) e order)
    (hof : ExactPositionOrder O (.node b r .nil) f order)
    (hre : ∀ s p q, (rel s).EvalAt (.node a l .nil) (binaryVal p q) ↔ G.rel s (e p) (e q)=true)
    (hrf : ∀ s p q, (rel s).EvalAt (.node b r .nil) (binaryVal p q) ↔ G.rel s (f p) (f q)=true)
    (hce : ∀ p : Position (.node a l .nil), p.label.toLabel.color=G.color (e p))
    (hcf : ∀ p : Position (.node b r .nil), p.label.toLabel.color=G.color (f p))
    (hne : (exactCodeSentence order rel).EvalAt (.node a l .nil) Fin.elim0)
    (hnf : (exactCodeSentence order rel).EvalAt (.node b r .nil) Fin.elim0) :
    BinaryTree.node a l .nil=BinaryTree.node b r .nil := by
  have se := (evalAt_normalizedOrderedSentence O _ e order hoe).mp hne.1
  have sf := (evalAt_normalizedOrderedSentence O _ f order hof).mp hnf.1
  exact normalized_graph_code_unique T O G a b l r e f order rel he hf
    ((siblingOrder_iff_strict O _ e).mpr se.2)
    ((siblingOrder_iff_strict O _ f).mpr sf.2) hoe hof hre hrf hce hcf hne.2 hnf.2

#print axioms exactCodeSentence_correct
#print axioms exact_sentence_graph_code_unique
end StackSorting.FinitePort.ChildSibling
