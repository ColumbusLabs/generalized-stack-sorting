import FiniteTreeLogicAtoms
import Mathlib.Data.Fintype.BigOperators

namespace StackSorting.TreeAutomaton.Logic
variable {α : Type}

instance : IsEmpty (Position (BinaryTree.nil : BinaryTree α)) := ⟨fun p => nomatch p⟩

def positionNodeEquiv (a : α) (l r : BinaryTree α) :
    Position (.node a l r) ≃ Option (Position l ⊕ Position r) where
  toFun
    | .root => none
    | .left p => some (.inl p)
    | .right p => some (.inr p)
  invFun
    | none => .root
    | some (.inl p) => .left p
    | some (.inr p) => .right p
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with _ | (_ | _) <;> rfl

instance positionFintype (t : BinaryTree α) : Fintype (Position t) := by
  induction t with
  | nil => exact Fintype.ofIsEmpty
  | node a l r hl hr =>
    letI := hl
    letI := hr
    exact Fintype.ofEquiv _ (positionNodeEquiv a l r).symm

open scoped BigOperators

theorem count_eq_position_sum (P : α → Bool) (t : BinaryTree α) :
    count P t = ∑ p : Position t, if P p.label then 1 else 0 := by
  classical
  induction t with
  | nil => simp [count]
  | node a l r hl hr =>
    rw [count, hl, hr, ← (positionNodeEquiv a l r).symm.sum_comp]
    simp [Fintype.sum_option, Fintype.sum_sum_type, positionNodeEquiv, Position.label,
      Nat.add_assoc]

/-- Singleton valuations mean exactly one actual internal-node position. -/
theorem count_one_iff_unique_position (P : α → Bool) (t : BinaryTree α) :
    count P t = 1 ↔ ∃! p : Position t, P p.label = true := by
  classical
  rw [Fintype.existsUnique_iff_card_one, count_eq_position_sum]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

#print axioms count_one_iff_unique_position
end StackSorting.TreeAutomaton.Logic

namespace StackSorting.TreeAutomaton.Logic
variable {α β : Type}

/-- Assign one value to every internal node, with no value at nil. -/
def annotate : (t : BinaryTree α) → (Position t → β) → BinaryTree (α × β)
  | .nil, _ => .nil
  | .node a l r, v => .node (a, v .root)
      (annotate l (fun p => v (.left p))) (annotate r (fun p => v (.right p)))

@[simp] theorem annotate_map_fst (t : BinaryTree α) (v : Position t → β) :
    (annotate t v).map Prod.fst = t := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [annotate, BinaryTree.map, hl, hr]

@[simp] theorem annotate_numNodes (t : BinaryTree α) (v : Position t → β) :
    (annotate t v).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [annotate, hl, hr]

/-- Relabelling lifts are exactly functions on existing internal-node positions. -/
theorem lift_eq_annotate (t : BinaryTree α) (u : BinaryTree (α × β))
    (h : u.map Prod.fst = t) : ∃ v : Position t → β, annotate t v = u := by
  induction t generalizing u with
  | nil =>
    cases u with
    | nil => exact ⟨(fun p => nomatch p), rfl⟩
    | node a l r => cases h
  | node a l r hl hr =>
    cases u with
    | nil => cases h
    | node c ul ur =>
      simp only [BinaryTree.map, BinaryTree.node.injEq] at h
      obtain ⟨hc, hll, hrr⟩ := h
      obtain ⟨vl, hvl⟩ := hl ul hll
      obtain ⟨vr, hvr⟩ := hr ur hrr
      refine ⟨fun p => match p with
        | .root => c.2
        | .left p => vl p
        | .right p => vr p, ?_⟩
      simp only [annotate, hvl, hvr]
      cases c
      simp_all

theorem exists_lift_iff_positions (t : BinaryTree α) (R : BinaryTree (α × β) → Prop) :
    (∃ u, u.map Prod.fst = t ∧ R u) ↔
      ∃ v : Position t → β, R (annotate t v) := by
  constructor
  · rintro ⟨u, hu, hR⟩
    obtain ⟨v, hv⟩ := lift_eq_annotate t u hu
    exact ⟨v, hv.symm ▸ hR⟩
  · rintro ⟨v, hR⟩
    exact ⟨annotate t v, annotate_map_fst t v, hR⟩

#print axioms exists_lift_iff_positions
end StackSorting.TreeAutomaton.Logic

namespace StackSorting.TreeAutomaton.Logic
variable {α : Type}

/-- The immediate ordered child relation on internal-node positions. -/
inductive Child : (right : Bool) → {t : BinaryTree α} → Position t → Position t → Prop
  | rootLeft {a b ll lr r} :
      Child false (t := .node a (.node b ll lr) r) .root (.left .root)
  | rootRight {a b l rl rr} :
      Child true (t := .node a l (.node b rl rr)) .root (.right .root)
  | left {d a l r} {p q : Position l} (h : Child d p q) :
      Child d (t := .node a l r) (.left p) (.left q)
  | right {d a l r} {p q : Position r} (h : Child d p q) :
      Child d (t := .node a l r) (.right p) (.right q)

theorem edge_iff_positions (d : Bool) (P : α → α → Bool) (t : BinaryTree α) :
    edge d P t = true ↔ ∃ p q : Position t, Child d p q ∧ P p.label q.label = true := by
  induction t with
  | nil =>
    constructor
    · simp [edge]
    · rintro ⟨p, _, _, _⟩; cases p
  | node a l r hl hr =>
    constructor
    · intro h
      simp only [edge, Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · cases d with
        | false =>
          cases l with
          | nil => simp [rootLabel] at h
          | node b ll lr => exact ⟨.root, .left .root, .rootLeft, h⟩
        | true =>
          cases r with
          | nil => simp [rootLabel] at h
          | node b rl rr => exact ⟨.root, .right .root, .rootRight, h⟩
      · obtain ⟨p, q, hC, hP⟩ := hl.mp h
        exact ⟨.left p, .left q, .left hC, hP⟩
      · obtain ⟨p, q, hC, hP⟩ := hr.mp h
        exact ⟨.right p, .right q, .right hC, hP⟩
    · rintro ⟨p, q, hC, hP⟩
      cases hC with
      | rootLeft =>
        simp only [Position.label] at hP
        simp [edge, rootLabel, hP]
      | rootRight =>
        simp only [Position.label] at hP
        simp [edge, rootLabel, hP]
      | left hC =>
        have h := hl.mpr ⟨_, _, hC, hP⟩
        simp [edge, h]
      | right hC =>
        have h := hr.mpr ⟨_, _, hC, hP⟩
        simp [edge, h]

#print axioms edge_iff_positions
end StackSorting.TreeAutomaton.Logic

namespace StackSorting.TreeAutomaton.Logic
variable {α β γ : Type}
open scoped BigOperators

theorem count_map (P : β → Bool) (f : α → β) (t : BinaryTree α) :
    count P (t.map f) = count (fun a => P (f a)) t := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [BinaryTree.map, count, hl, hr]

theorem count_annotate (P : α × β → Bool) (t : BinaryTree α) (v : Position t → β) :
    count P (annotate t v) = ∑ p : Position t, if P (p.label, v p) then 1 else 0 := by
  classical
  induction t with
  | nil => simp [annotate, count]
  | node a l r hl hr =>
    simp only [annotate, count, hl, hr]
    rw [← (positionNodeEquiv a l r).symm.sum_comp]
    simp [Fintype.sum_option, Fintype.sum_sum_type, positionNodeEquiv, Position.label,
      Nat.add_assoc]

theorem annotate_singleton_iff (t : BinaryTree α) (v : Position t → Bool) :
    count Prod.snd (annotate t v) = 1 ↔ ∃! p : Position t, v p = true := by
  classical
  rw [Fintype.existsUnique_iff_card_one, count_annotate]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
end StackSorting.TreeAutomaton.Logic
