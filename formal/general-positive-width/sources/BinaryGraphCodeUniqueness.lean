import BinaryNormalPortRecognition

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic SparseTreeCompiler

/-- Once the parent tree and independent chronology are fixed on the original
vertices, the literal port sentence removes every remaining label choice.
Combined with the exact binary inverse, this gives equality of the actual
trees, even when colors and all stored relation bits repeat. -/
theorem normalized_graph_code_unique {n colors relations W}
    (T : RootedTree n) (O : FixedOrder n) (G : Diagram n colors relations)
    (a b : Alphabet colors relations W)
    (l r : BinaryTree (Alphabet colors relations W))
    (e : Position (.node a l .nil) ≃ Fin n)
    (f : Position (.node b r .nil) ≃ Fin n)
    (order : Formula (Alphabet colors relations W) 2)
    (rel : Fin relations → Formula (Alphabet colors relations W) 2)
    (he : ∀ p q, ParentPosition p q ↔ (e q).val≠0 ∧ T.parent (e q)=e p)
    (hf : ∀ p q, ParentPosition p q ↔ (f q).val≠0 ∧ T.parent (f q)=f p)
    (oe : SiblingOrderCompatible O (.node a l .nil) e)
    (of : SiblingOrderCompatible O (.node b r .nil) f)
    (hoe : ∀ p q, order.EvalAt (.node a l .nil) (binaryVal p q) ↔
      O.vertices.idxOf (e p)<O.vertices.idxOf (e q))
    (hof : ∀ p q, order.EvalAt (.node b r .nil) (binaryVal p q) ↔
      O.vertices.idxOf (f p)<O.vertices.idxOf (f q))
    (hre : ∀ s p q, (rel s).EvalAt (.node a l .nil) (binaryVal p q) ↔ G.rel s (e p) (e q)=true)
    (hrf : ∀ s p q, (rel s).EvalAt (.node b r .nil) (binaryVal p q) ↔ G.rel s (f p) (f q)=true)
    (hce : ∀ p, p.label.toLabel.color=G.color (e p))
    (hcf : ∀ p, p.label.toLabel.color=G.color (f p))
    (hne : (normalSlotsFormula parentRoute order rel).EvalAt (.node a l .nil) Fin.elim0)
    (hnf : (normalSlotsFormula parentRoute order rel).EvalAt (.node b r .nil) Fin.elim0) :
    BinaryTree.node a l .nil=BinaryTree.node b r .nil := by
  apply normalized_unique T O a b l r e f he hf oe of
  intro i
  apply Alphabet.toLabel_injective
  have hE := (indexed_normalSlots_correct T O G (.node a l .nil) e order rel he hoe hre hce).mp hne
  have hF := (indexed_normalSlots_correct T O G (.node b r .nil) f order rel hf hof hrf hcf).mp hnf
  change labelCode (indexedLabels (.node a l .nil) e) i =
    labelCode (indexedLabels (.node b r .nil) f) i
  rw [hE,hF]

#print axioms normalized_graph_code_unique
end StackSorting.FinitePort.ChildSibling
