import PortNormalFormSyntaxCompleteness
import BinaryCodeFormulaTransport
import BinaryNormalReconstruction

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic SparseTreeCompiler
variable {α : Type} {n colors relations W : Nat}

noncomputable def indexedLabels (t : BinaryTree α) (e : Position t ≃ Fin n) : Fin n → α :=
  fun i => (e.symm i).label

noncomputable def indexedChildren (t : BinaryTree α) (e : Position t ≃ Fin n) :
    Bool → Fin n → Fin n → Prop := fun d i j => Child d (e.symm i) (e.symm j)

theorem eval_indexed_two (t : BinaryTree α) (e : Position t ≃ Fin n)
    (f : Formula α 2) (p q : Position t) :
    f.EvalAt t (binaryVal p q) ↔
      f.EvalOn (indexedLabels t e) (indexedChildren t e) (binaryVal (e p) (e q)) := by
  apply f.evalOn_equiv e
  · intro x; simp only [indexedLabels,Equiv.symm_apply_apply]
  · intro d x y; simp only [indexedChildren,Equiv.symm_apply_apply]
  · exact binaryVal_equiv e p q

theorem eval_indexed_sentence (t : BinaryTree α) (e : Position t ≃ Fin n)
    (f : Formula α 0) :
    f.EvalAt t Fin.elim0 ↔ f.EvalOn (indexedLabels t e) (indexedChildren t e) Fin.elim0 := by
  apply f.evalOn_equiv e
  · intro x; simp only [indexedLabels,Equiv.symm_apply_apply]
  · intro d x y; simp only [indexedChildren,Equiv.symm_apply_apply]
  · intro i; exact Fin.elim0 i

theorem indexed_exact_parent (T : RootedTree n) (t : BinaryTree (Alphabet colors relations W))
    (e : Position t ≃ Fin n)
    (hp : ∀ p q, ParentPosition p q ↔ (e q).val≠0 ∧ T.parent (e q)=e p) :
    ExactParent T (indexedLabels t e) (indexedChildren t e) parentRoute := by
  intro p q
  have ht := eval_indexed_two t e parentRoute (e.symm p) (e.symm q)
  simp only [Equiv.apply_symm_apply] at ht
  rw [←ht]
  change parentRoute.EvalOn Position.label (fun d u v => Child d u v)
    (binaryVal (e.symm p) (e.symm q)) ↔ _
  rw [parentRoute_correct,hp]
  simp only [Equiv.apply_symm_apply,eq_comm]

/-- Literal normal-form recognition on actual binary positions. The proper
parent formula is fixed syntax; the hypotheses name the original graph,
chronology and parent structure represented by the positions. -/
theorem indexed_normalSlots_correct (T : RootedTree n) (O : FixedOrder n)
    (G : Diagram n colors relations) (t : BinaryTree (Alphabet colors relations W))
    (e : Position t ≃ Fin n) (order : Formula (Alphabet colors relations W) 2)
    (rel : Fin relations → Formula (Alphabet colors relations W) 2)
    (hp : ∀ p q, ParentPosition p q ↔ (e q).val≠0 ∧ T.parent (e q)=e p)
    (ho : ∀ p q, order.EvalAt t (binaryVal p q) ↔ O.vertices.idxOf (e p)<O.vertices.idxOf (e q))
    (hr : ∀ r p q, (rel r).EvalAt t (binaryVal p q) ↔ G.rel r (e p) (e q)=true)
    (hc : ∀ p, p.label.toLabel.color=G.color (e p)) :
    (normalSlotsFormula parentRoute order rel).EvalAt t Fin.elim0 ↔
      labelCode (indexedLabels t e)=encode T O G := by
  rw [eval_indexed_sentence t e]
  apply normalSlotsFormula_correct T G O (indexedLabels t e) (indexedChildren t e)
    parentRoute order rel (indexed_exact_parent T t e hp)
  · intro u v
    have he := eval_indexed_two t e order (e.symm u) (e.symm v)
    simp only [Equiv.apply_symm_apply] at he
    rw [←he,ho]
    simp only [Equiv.apply_symm_apply]
  · intro r u v
    have he := eval_indexed_two t e (rel r) (e.symm u) (e.symm v)
    simp only [Equiv.apply_symm_apply] at he
    rw [←he,hr]
    simp only [Equiv.apply_symm_apply]
  · intro v
    simpa only [indexedLabels,Equiv.apply_symm_apply] using hc (e.symm v)

/-- No supplied parent tree or parent interpretation is needed on a normalized
nonempty binary shape: both are reconstructed from its actual positions. -/
theorem normal_binary_slots_correct
    (a : Alphabet colors relations W) (l : BinaryTree (Alphabet colors relations W))
    (O : FixedOrder (BinaryTree.node a l .nil).numNodes)
    (G : Diagram (BinaryTree.node a l .nil).numNodes colors relations)
    (order : Formula (Alphabet colors relations W) 2)
    (rel : Fin relations → Formula (Alphabet colors relations W) 2)
    (ho : ∀ p q : Position (.node a l .nil), order.EvalAt (.node a l .nil) (binaryVal p q) ↔
      O.vertices.idxOf (positionIndexEquiv _ p)<O.vertices.idxOf (positionIndexEquiv _ q))
    (hr : ∀ r p q, (rel r).EvalAt (.node a l .nil) (binaryVal p q) ↔
      G.rel r (positionIndexEquiv _ p) (positionIndexEquiv _ q)=true)
    (hc : ∀ p, p.label.toLabel.color=G.color (positionIndexEquiv _ p)) :
    (normalSlotsFormula parentRoute order rel).EvalAt (.node a l .nil) Fin.elim0 ↔
      labelCode (indexedLabels (.node a l .nil) (positionIndexEquiv _))=
        encode (normalPositionTree a l) O G := by
  exact indexed_normalSlots_correct (normalPositionTree a l) O G (.node a l .nil)
    (positionIndexEquiv _) order rel
    (fun p q => (normalPositionTree_exact_parent a l p q).symm) ho hr hc

#print axioms indexed_normalSlots_correct
#print axioms normal_binary_slots_correct
end StackSorting.FinitePort.ChildSibling
