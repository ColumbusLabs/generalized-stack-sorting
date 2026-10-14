import FiniteTreeLogicAtoms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

namespace StackSorting.TreeAutomaton
namespace Logic

variable (α : Type)
/-- A label together with truth values of n monadic variables at that internal node. -/
abbrev Marked (n : Nat) := α × (Fin n → Bool)

/-- All atoms are interpreted over internal nodes. First-order variables are
represented by singleton monadic variables; equality is mutual inclusion. -/
inductive Atom (n : Nat)
  | subset (i j : Fin n)
  | label (i : Fin n) (a : α)
  | singleton (i : Fin n)
  | child (right : Bool) (i j : Fin n)

/-- Finite-tree MSO with explicit first- and second-order existential binders.
A new binder occupies index zero and the previous variables shift by one. -/
inductive Formula : Nat → Type
  | atom {n} : Atom α n → Formula n
  | neg {n} : Formula n → Formula n
  | conj {n} : Formula n → Formula n → Formula n
  | existsSet {n} : Formula (n+1) → Formula n
  | existsFirst {n} : Formula (n+1) → Formula n

variable {α}

def extend {n : Nat} (a : Marked α n × Bool) : Marked α (n+1) :=
  (a.1.1, Fin.cons a.2 a.1.2)

variable [DecidableEq α]

def Atom.Holds {n : Nat} : Atom α n → BinaryTree (Marked α n) → Prop
  | .subset i j, t => all (fun a => !a.2 i || a.2 j) t = true
  | .label i c, t => all (fun a => !a.2 i || decide (a.1 = c)) t = true
  | .singleton i, t => count (fun a => a.2 i) t = 1
  | .child right i j, t => edge right (fun a b => a.2 i && b.2 j) t = true

/-- Existential set valuations label precisely the existing internal nodes.
There is a unique lift of nil, so second-order quantification on nil ranges
only over the empty set, and first-order quantification on nil is false. -/
def Formula.Holds : {n : Nat} → Formula α n → BinaryTree (Marked α n) → Prop
  | _, .atom a, t => a.Holds t
  | _, .neg p, t => ¬ p.Holds t
  | _, .conj p q, t => p.Holds t ∧ q.Holds t
  | _, .existsSet p, t => ∃ u : BinaryTree (Marked α _ × Bool),
      u.map Prod.fst = t ∧ p.Holds (u.map extend)
  | _, .existsFirst p, t => ∃ u : BinaryTree (Marked α _ × Bool),
      u.map Prod.fst = t ∧ count (fun a => a.2 (0 : Fin (_+1))) (u.map extend) = 1 ∧
      p.Holds (u.map extend)

variable [Fintype α]

theorem Atom.recognizable {n : Nat} (a : Atom α n) : Recognizable {t | a.Holds t} := by
  cases a with
  | subset i j => exact recognizable_all _
  | label i c => exact recognizable_all _
  | singleton i => exact recognizable_singleton _
  | child right i j => exact recognizable_edge _ _

/-- Constructive-in-the-formula finite-state recognizability: products implement
conjunction, accepting-set complement implements negation, and projection uses
explicit powerset determinization. No recognizability premise is assumed. -/
theorem Formula.recognizable {n : Nat} (p : Formula α n) :
    Recognizable {t | p.Holds t} := by
  induction p with
  | atom a => exact a.recognizable
  | neg p hp => exact hp.compl
  | conj p q hp hq => exact hp.inter hq
  | existsSet p hp =>
    have h := (hp.preimage extend).project
    simpa only [Set.mem_ofPred_eq, Formula.Holds, and_comm] using h
  | @existsFirst n p hp =>
    have hs : Recognizable {t : BinaryTree (Marked α (n+1)) |
      count (fun a => a.2 (0 : Fin (n+1))) t = 1} := recognizable_singleton _
    have h := ((hs.inter hp).preimage extend).project
    simpa only [Set.mem_ofPred_eq, Set.mem_inter_iff, Formula.Holds, and_comm] using h

omit [Fintype α] in
@[simp] theorem Formula.existsFirst_nil {n : Nat} (p : Formula α (n+1)) :
    ¬ (Formula.existsFirst p).Holds .nil := by
  rintro ⟨u, hu, hc, _⟩
  cases u with
  | nil => simp [BinaryTree.map, count] at hc
  | node a l r => cases hu

omit [Fintype α] in
@[simp] theorem Formula.existsSet_nil {n : Nat} (p : Formula α (n+1)) :
    (Formula.existsSet p).Holds .nil ↔ p.Holds .nil := by
  constructor
  · rintro ⟨u, hu, hp⟩
    cases u with
    | nil => exact hp
    | node a l r => cases hu
  · intro h
    exact ⟨.nil, rfl, h⟩

#print axioms Formula.recognizable
#print axioms Formula.existsFirst_nil
end Logic
end StackSorting.TreeAutomaton
