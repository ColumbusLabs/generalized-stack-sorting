import BinarySiblingEdgeOrder
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto

set_option warningAsError true

namespace StackSorting.FinitePort.ChildSibling.BinaryOrderMSO
open TreeAutomaton.Logic SparseTreeCompiler
variable {α P : Type}

/-- Plain finite-tree syntax for implication. -/
def implies {k : Nat} (f g : Formula α k) : Formula α k :=
  .neg (.conj f (.neg g))

/-- Plain finite-tree syntax for disjunction. -/
def either {k : Nat} (f g : Formula α k) : Formula α k :=
  .neg (.conj (.neg f) (.neg g))

theorem eval_implies {k : Nat} (label : P → α) (child : Bool → P → P → Prop)
    (v : Fin k → P → Bool) (f g : Formula α k) :
    (implies f g).EvalOn label child v ↔
      (f.EvalOn label child v → g.EvalOn label child v) := by
  classical
  simp [implies, Formula.EvalOn]

theorem eval_either {k : Nat} (label : P → α) (child : Bool → P → P → Prop)
    (v : Fin k → P → Bool) (f g : Formula α k) :
    (either f g).EvalOn label child v ↔
      (f.EvalOn label child v ∨ g.EvalOn label child v) := by
  classical
  simp only [either, Formula.EvalOn]
  tauto

/-- Free variables 0 and 1 denote a binary edge's source and target. Inside
existsFirst, 0 is the predecessor and 1 is the old source. -/
def shapeBody : Formula α 2 :=
  implies (.atom (.child true 0 1))
    (.existsFirst (either (.atom (.child false 0 1)) (.atom (.child true 0 1))))

def normalizedShapeSentence : Formula α 0 := allBlock 2 shapeBody

/-- Endpoints of parentRoute are p,q; the literal right edge is q,z; the
order formula is evaluated at q,z. The forest-root chain is not constrained. -/
def siblingBody (order : Formula α 2) : Formula α 3 :=
  implies (.conj (parentRoute.rename (Fin.cons 0 (fun _ => 1)))
      (.atom (.child true 1 2)))
    (order.rename (Fin.cons 1 (fun _ => 2)))

def siblingOrderSentence (order : Formula α 2) : Formula α 0 :=
  allBlock 3 (siblingBody order)

/-- Literal normalized first-child/next-sibling shape and chronological
sibling order; all quantifiers range over actual internal-node positions. -/
def normalizedOrderedSentence (order : Formula α 2) : Formula α 0 :=
  .conj normalizedShapeSentence (siblingOrderSentence order)

private theorem eval_closedBlock {k : Nat} (label : P → α)
    (child : Bool → P → P → Prop) (f : Formula α k) :
    (allBlock k f).EvalOn label child Fin.elim0 ↔
      ∀ xs : Fin k → P, f.EvalOn label child (fun i => point (xs i)) := by
  rw [eval_allBlock]
  simp

/-- Singleton-valued child atoms test the exact indicated endpoints. -/
theorem eval_pointChild {k : Nat} (label : P → α)
    (child : Bool → P → P → Prop) (v : Fin k → P → Bool)
    (d : Bool) (i j : Fin k) (p q : P) (hi : v i = point p) (hj : v j = point q) :
    (Formula.atom (.child d i j)).EvalOn label child v ↔ child d p q := by
  classical
  simp [Formula.EvalOn, Atom.EvalOn, hi, hj, point]

/-- Renaming preserves both endpoint order and all internal quantifier scopes. -/
theorem eval_pointRename {k : Nat} (label : P → α)
    (child : Bool → P → P → Prop) (f : Formula α 2)
    (v : Fin k → P → Bool) (i j : Fin k) (p q : P)
    (hi : v i = point p) (hj : v j = point q) :
    (f.rename (Fin.cons i (fun _ => j))).EvalOn label child v ↔
      f.EvalOn label child (binaryVal p q) := by
  rw [Formula.evalOn_rename]
  have he : (fun z => v ((Fin.cons i (fun _ => j) : Fin 2 → Fin k) z)) =
      binaryVal p q := by
    funext z
    fin_cases z <;> simp [binaryVal,hi,hj]
  rw [he]

/-- Arbitrary-carrier semantics of the shape syntax. -/
theorem eval_shapeBody (label : P → α) (child : Bool → P → P → Prop)
    (xs : Fin 2 → P) :
    shapeBody.EvalOn label child (fun i => point (xs i)) ↔
      (child true (xs 0) (xs 1) → ∃ p, child false p (xs 0) ∨ child true p (xs 0)) := by
  classical
  rw [shapeBody,eval_implies,eval_pointChild label child _ true 0 1 _ _ rfl rfl]
  apply imp_congr_right
  intro _
  rw [Formula.evalOn_existsFirst]
  apply exists_congr
  intro p
  rw [eval_either]
  have hp : (fun y => decide (y=p))=point p := by
    funext y
    simp only [point]
  rw [hp]
  rw [eval_pointChild label child _ false 0 1 p (xs 0) rfl rfl,
    eval_pointChild label child _ true 0 1 p (xs 0) rfl rfl]

theorem evalOn_normalizedShapeSentence (t : BinaryTree α) :
    normalizedShapeSentence.EvalOn Position.label (fun d p q => Child d p q)
      (Fin.elim0 : Fin 0 → Position t → Bool) ↔ NormalizedBinaryShape t := by
  rw [normalizedShapeSentence,eval_closedBlock]
  simp only [eval_shapeBody]
  rw [normalizedBinaryShape_iff_edges]
  constructor
  · intro h p q he
    exact h (Fin.cons p (fun _ => q)) he
  · intro h xs he
    exact h (xs 0) (xs 1) he

theorem evalAt_normalizedShapeSentence (t : BinaryTree α) :
    normalizedShapeSentence.EvalAt t Fin.elim0 ↔ NormalizedBinaryShape t :=
  evalOn_normalizedShapeSentence t

/-- Exact order interpretation on any map of positions to an independent
chronology. No bijection, shape witness, or recognizability hypothesis is used. -/
def ExactPositionOrder {n : Nat} (O : FixedOrder n) (t : BinaryTree α)
    (e : Position t → Fin n) (order : Formula α 2) : Prop :=
  ∀ p q, order.EvalOn Position.label (fun d u v => Child d u v) (binaryVal p q) ↔
    OrderBefore O (e p) (e q)

/-- Raw semantics without any order assumption, useful for binding controls. -/
theorem eval_siblingBody_relation (t : BinaryTree α) (order : Formula α 2)
    (xs : Fin 3 → Position t) :
    (siblingBody order).EvalOn Position.label (fun d p q => Child d p q)
      (fun i => point (xs i)) ↔
      (ParentPosition (xs 0) (xs 1) → Child true (xs 1) (xs 2) →
        order.EvalAt t (binaryVal (xs 1) (xs 2))) := by
  rw [siblingBody,eval_implies,Formula.EvalOn]
  rw [eval_pointRename Position.label _ _ _ 0 1 (xs 0) (xs 1) rfl rfl,
    parentRoute_correct]
  rw [eval_pointChild Position.label _ _ true 1 2 (xs 1) (xs 2) rfl rfl]
  rw [eval_pointRename Position.label _ _ _ 1 2 (xs 1) (xs 2) rfl rfl]
  exact and_imp

theorem evalOn_siblingOrderSentence_relation (t : BinaryTree α) (order : Formula α 2) :
    (siblingOrderSentence order).EvalOn Position.label (fun d p q => Child d p q)
      (Fin.elim0 : Fin 0 → Position t → Bool) ↔
      ∀ p q z, ParentPosition p q → Child true q z → order.EvalAt t (binaryVal q z) := by
  rw [siblingOrderSentence,eval_closedBlock]
  simp only [eval_siblingBody_relation]
  constructor
  · intro h p q z hp he
    exact h (Fin.cons p (Fin.cons q (fun _ => z))) hp he
  · intro h xs hp he
    exact h (xs 0) (xs 1) (xs 2) hp he

theorem eval_siblingBody {n : Nat} (O : FixedOrder n) (t : BinaryTree α)
    (e : Position t → Fin n) (order : Formula α 2)
    (ho : ExactPositionOrder O t e order) (xs : Fin 3 → Position t) :
    (siblingBody order).EvalOn Position.label (fun d p q => Child d p q)
      (fun i => point (xs i)) ↔
      (ParentPosition (xs 0) (xs 1) → Child true (xs 1) (xs 2) →
        OrderBefore O (e (xs 1)) (e (xs 2))) := by
  rw [siblingBody,eval_implies,Formula.EvalOn]
  rw [eval_pointRename Position.label _ _ _ 0 1 (xs 0) (xs 1) rfl rfl,
    parentRoute_correct]
  rw [eval_pointChild Position.label _ _ true 1 2 (xs 1) (xs 2) rfl rfl]
  rw [eval_pointRename Position.label _ _ _ 1 2 (xs 1) (xs 2) rfl rfl, ho]
  exact and_imp

theorem evalOn_siblingOrderSentence {n : Nat} (O : FixedOrder n) (t : BinaryTree α)
    (e : Position t → Fin n) (order : Formula α 2)
    (ho : ExactPositionOrder O t e order) :
    (siblingOrderSentence order).EvalOn Position.label (fun d p q => Child d p q)
      (Fin.elim0 : Fin 0 → Position t → Bool) ↔ SiblingOrderStrict O t e := by
  rw [siblingOrderSentence,eval_closedBlock]
  simp only [eval_siblingBody O t e order ho]
  rw [siblingOrderStrict_iff_edges]
  constructor
  · intro h p q z hp he
    exact h (Fin.cons p (Fin.cons q (fun _ => z))) hp he
  · intro h xs hp he
    exact h (xs 0) (xs 1) (xs 2) hp he

theorem evalAt_siblingOrderSentence {n : Nat} (O : FixedOrder n) (t : BinaryTree α)
    (e : Position t → Fin n) (order : Formula α 2)
    (ho : ExactPositionOrder O t e order) :
    (siblingOrderSentence order).EvalAt t Fin.elim0 ↔ SiblingOrderStrict O t e :=
  evalOn_siblingOrderSentence O t e order ho

theorem evalOn_normalizedOrderedSentence {n : Nat} (O : FixedOrder n) (t : BinaryTree α)
    (e : Position t → Fin n) (order : Formula α 2)
    (ho : ExactPositionOrder O t e order) :
    (normalizedOrderedSentence order).EvalOn Position.label (fun d p q => Child d p q)
      (Fin.elim0 : Fin 0 → Position t → Bool) ↔
      NormalizedBinaryShape t ∧ SiblingOrderStrict O t e := by
  rw [normalizedOrderedSentence,Formula.EvalOn,evalOn_normalizedShapeSentence,
    evalOn_siblingOrderSentence O t e order ho]

theorem evalAt_normalizedOrderedSentence {n : Nat} (O : FixedOrder n) (t : BinaryTree α)
    (e : Position t → Fin n) (order : Formula α 2)
    (ho : ExactPositionOrder O t e order) :
    (normalizedOrderedSentence order).EvalAt t Fin.elim0 ↔
      NormalizedBinaryShape t ∧ SiblingOrderStrict O t e :=
  evalOn_normalizedOrderedSentence O t e order ho

#print axioms evalOn_normalizedShapeSentence
#print axioms evalOn_siblingOrderSentence
#print axioms evalOn_normalizedOrderedSentence
#print axioms evalAt_normalizedOrderedSentence
end StackSorting.FinitePort.ChildSibling.BinaryOrderMSO
