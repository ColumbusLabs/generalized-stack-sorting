import BinaryParentPositions
import Mathlib.Logic.Relation

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type}

abbrev RightReach {t : BinaryTree α} := Relation.ReflTransGen (Child (t := t) true)

theorem rootSibling_step {t : BinaryTree α} {p q : Position t}
    (h : RootSibling p) (edge : Child true p q) : RootSibling q := by
  induction h with
  | root => cases edge with | rootRight => exact .right .root
  | right h ih => cases edge with | right e => exact .right (ih e)

inductive RootPosition : {t : BinaryTree α} → Position t → Prop
  | root {a l r} : RootPosition (t := .node a l r) .root

theorem rootSibling_has_root {t : BinaryTree α} {p : Position t}
    (h : RootSibling p) : ∃ q, RootPosition q ∧ RightReach q p := by
  induction h with
  | root => exact ⟨.root,.root,.refl⟩
  | right h ih =>
    obtain ⟨q,hq,hp⟩ := ih
    cases hq with
    | root => exact ⟨.root,.root,Relation.ReflTransGen.head Child.rootRight
        (hp.lift Position.right (fun _ _ e => Child.right e))⟩

theorem rootSibling_chain {a : α} {l r : BinaryTree α}
    {p : Position (.node a l r)} (h : RootSibling p) : RightReach .root p := by
  obtain ⟨q,hq,hp⟩ := rootSibling_has_root h
  cases hq
  exact hp

theorem parentPosition_step {t : BinaryTree α} {p q z : Position t}
    (h : ParentPosition p q) (edge : Child true q z) : ParentPosition p z := by
  induction h with
  | root h => cases edge with | left e => exact .root (rootSibling_step h e)
  | left h ih => cases edge with | left e => exact .left (ih e)
  | right h ih => cases edge with | right e => exact .right (ih e)

theorem childLeft_parent {t : BinaryTree α} {p q : Position t}
    (h : Child false p q) : ParentPosition p q := by
  induction t with
  | nil => cases p
  | node a l r hl hr =>
    cases h with
    | rootLeft => exact .root .root
    | left h => exact .left (hl h)
    | right h => exact .right (hr h)

/-- Exact first-child then next-sibling reachability on actual positions. -/
theorem parentPosition_iff_reach {t : BinaryTree α} (p q : Position t) :
    ParentPosition p q ↔ ∃ z, Child false p z ∧ RightReach z q := by
  constructor
  · intro h
    induction h with
    | @root a l r q h =>
      cases l with
      | nil => cases q
      | node b ll lr =>
        exact ⟨.left .root,.rootLeft,
          (rootSibling_chain h).lift Position.left (fun _ _ e => Child.left e)⟩
    | left h ih =>
      obtain ⟨z,hz,hq⟩ := ih
      exact ⟨.left z,.left hz,hq.lift Position.left (fun _ _ e => Child.left e)⟩
    | right h ih =>
      obtain ⟨z,hz,hq⟩ := ih
      exact ⟨.right z,.right hz,hq.lift Position.right (fun _ _ e => Child.right e)⟩
  · rintro ⟨z,hz,hq⟩
    have hp := childLeft_parent hz
    induction hq with
    | refl => exact hp
    | tail h e ih => exact parentPosition_step ih e

#print axioms parentPosition_iff_reach
end StackSorting.FinitePort.ChildSibling
