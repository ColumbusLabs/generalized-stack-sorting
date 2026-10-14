import FiniteTreeAutomatonClosure
import Mathlib.Data.Fintype.Option

namespace StackSorting.TreeAutomaton
namespace Logic

variable {α : Type}

/-- Internal-node addresses only: nil has no position. -/
inductive Position : BinaryTree α → Type
  | root {a l r} : Position (.node a l r)
  | left {a l r} : Position l → Position (.node a l r)
  | right {a l r} : Position r → Position (.node a l r)

def Position.label : {t : BinaryTree α} → Position t → α
  | .node a _ _, .root => a
  | .node _ _ _, .left p => p.label
  | .node _ _ _, .right p => p.label

/-- Literal count of marked internal nodes. -/
def count (P : α → Bool) : BinaryTree α → Nat
  | .nil => 0
  | .node a l r => (if P a then 1 else 0) + count P l + count P r

def all (P : α → Bool) : BinaryTree α → Bool
  | .nil => true
  | .node a l r => P a && all P l && all P r

def allAutomaton (P : α → Bool) : Automaton α Bool where
  emptyState := true
  step a l r := P a && l && r

@[simp] theorem run_allAutomaton (P : α → Bool) (t : BinaryTree α) :
    (allAutomaton P).run t = all P t := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp only [Automaton.run, hl, hr]; rfl

theorem recognizable_all (P : α → Bool) : Recognizable {t | all P t = true} :=
  ⟨Bool, inferInstance, allAutomaton P, {true}, fun t => by simp⟩

theorem all_iff_positions (P : α → Bool) (t : BinaryTree α) :
    all P t = true ↔ ∀ p : Position t, P p.label = true := by
  induction t with
  | nil => simp [all]; intro p; cases p
  | node a l r hl hr =>
    simp only [all, Bool.and_eq_true, hl, hr]
    constructor
    · rintro ⟨⟨ha, hl⟩, hr⟩ p
      cases p with
      | root => exact ha
      | left p => exact hl p
      | right p => exact hr p
    · intro h
      exact ⟨⟨h .root, fun p => h (.left p)⟩, fun p => h (.right p)⟩

/-- Three-state counter: 0, 1, or at least 2 marked internal nodes. -/
def countAutomaton (P : α → Bool) : Automaton α (Fin 3) where
  emptyState := 0
  step a l r := ⟨min 2 ((if P a then 1 else 0) + l.val + r.val), by omega⟩

theorem run_countAutomaton (P : α → Bool) (t : BinaryTree α) :
    ((countAutomaton P).run t).val = min 2 (count P t) := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    change min 2 ((if P a then 1 else 0) + _ + _) = _
    rw [hl, hr]
    simp only [count]
    split <;> omega

theorem recognizable_singleton (P : α → Bool) : Recognizable {t | count P t = 1} := by
  refine ⟨Fin 3, inferInstance, countAutomaton P, {q | q.val = 1}, ?_⟩
  intro t
  change count P t = 1 ↔ ((countAutomaton P).run t).val = 1
  rw [run_countAutomaton]
  omega

/-- Tree root label, absent exactly for the empty tree. -/
def rootLabel : BinaryTree α → Option α
  | .nil => none
  | .node a _ _ => some a

/-- A witnessed left or right parent-child edge with endpoint-label predicate. -/
def edge (right : Bool) (P : α → α → Bool) : BinaryTree α → Bool
  | .nil => false
  | .node a l r =>
    (match rootLabel (if right then r else l) with
      | none => false
      | some b => P a b) || edge right P l || edge right P r

def edgeAutomaton (right : Bool) (P : α → α → Bool) : Automaton α (Option α × Bool) where
  emptyState := (none, false)
  step a l r := (some a,
    (match (if right then r.1 else l.1) with
      | none => false
      | some b => P a b) || l.2 || r.2)

theorem run_edgeAutomaton (right : Bool) (P : α → α → Bool) (t : BinaryTree α) :
    (edgeAutomaton right P).run t = (rootLabel t, edge right P t) := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    simp only [Automaton.run, hl, hr]
    cases right <;> rfl

theorem recognizable_edge [Fintype α] (right : Bool) (P : α → α → Bool) :
    Recognizable {t | edge right P t = true} := by
  refine ⟨Option α × Bool, inferInstance, edgeAutomaton right P,
    {q | q.2 = true}, ?_⟩
  intro t
  change edge right P t = true ↔ ((edgeAutomaton right P).run t).2 = true
  rw [run_edgeAutomaton]

#print axioms recognizable_singleton
#print axioms all_iff_positions
#print axioms recognizable_edge
end Logic
end StackSorting.TreeAutomaton
