import FiniteLabelledTreeEnumeration
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

namespace StackSorting.TreeAutomaton

variable {α β Q R : Type*}

/-- Product construction for simultaneous deterministic runs. -/
def Automaton.prod (A : Automaton α Q) (B : Automaton α R) : Automaton α (Q × R) where
  emptyState := (A.emptyState, B.emptyState)
  step a q r := (A.step a q.1 r.1, B.step a q.2 r.2)

@[simp] theorem Automaton.run_prod (A : Automaton α Q) (B : Automaton α R)
    (t : BinaryTree α) : (A.prod B).run t = (A.run t, B.run t) := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp only [Automaton.run, hl, hr]; rfl

/-- Recognition requires an actual finite state type and literal bottom-up run. -/
def Recognizable (L : Set (BinaryTree α)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (A : Automaton α Q) (F : Set Q),
    ∀ t, t ∈ L ↔ A.run t ∈ F

theorem Recognizable.compl {L : Set (BinaryTree α)} (h : Recognizable L) :
    Recognizable Lᶜ := by
  obtain ⟨Q, hQ, A, F, h⟩ := h
  exact ⟨Q, hQ, A, Fᶜ, fun t => not_congr (h t)⟩

theorem Recognizable.inter {L M : Set (BinaryTree α)}
    (hL : Recognizable L) (hM : Recognizable M) : Recognizable (L ∩ M) := by
  obtain ⟨Q, hQ, A, F, hA⟩ := hL
  obtain ⟨R, hR, B, G, hB⟩ := hM
  let _ := hQ
  let _ := hR
  refine ⟨Q × R, inferInstance, A.prod B, {p | p.1 ∈ F ∧ p.2 ∈ G}, ?_⟩
  intro t
  simpa using and_congr (hA t) (hB t)

def Automaton.relabel (A : Automaton β Q) (f : α → β) : Automaton α Q where
  emptyState := A.emptyState
  step a := A.step (f a)

@[simp] theorem Automaton.run_relabel (A : Automaton β Q) (f : α → β)
    (t : BinaryTree α) : (A.relabel f).run t = A.run (t.map f) := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp only [Automaton.run, BinaryTree.map, hl, hr]; rfl

theorem Recognizable.preimage {L : Set (BinaryTree β)} (h : Recognizable L)
    (f : α → β) : Recognizable {t | t.map f ∈ L} := by
  obtain ⟨Q, hQ, A, F, hA⟩ := h
  exact ⟨Q, hQ, A.relabel f, F, fun t => by simpa using hA (t.map f)⟩

/-- Subset determinization of independent existential choices at each internal node.
The empty tree has exactly the singleton original empty state. -/
def Automaton.project (A : Automaton (α × β) Q) : Automaton α (Set Q) where
  emptyState := {A.emptyState}
  step a l r := {q | ∃ b ql qr, ql ∈ l ∧ qr ∈ r ∧ A.step (a,b) ql qr = q}

/-- Projection is existential relabelling of the same literal tree, including nil. -/
theorem Automaton.mem_run_project (A : Automaton (α × β) Q)
    (t : BinaryTree α) (q : Q) :
    q ∈ A.project.run t ↔
      ∃ u : BinaryTree (α × β), u.map Prod.fst = t ∧ A.run u = q := by
  induction t generalizing q with
  | nil =>
    constructor
    · intro h
      exact ⟨.nil, rfl, h.symm⟩
    · rintro ⟨u, hu, hq⟩
      cases u with
      | nil => exact hq.symm
      | node a l r => cases hu
  | node a l r hl hr =>
    change (∃ b ql qr, ql ∈ A.project.run l ∧ qr ∈ A.project.run r ∧
      A.step (a,b) ql qr = q) ↔ _
    constructor
    · rintro ⟨b, ql, qr, hql, hqr, hq⟩
      obtain ⟨ul, hul, hrl⟩ := (hl ql).mp hql
      obtain ⟨ur, hur, hrr⟩ := (hr qr).mp hqr
      refine ⟨.node (a,b) ul ur, ?_, ?_⟩
      · simp [BinaryTree.map, hul, hur]
      · simpa [Automaton.run, hrl, hrr] using hq
    · rintro ⟨u, hu, hq⟩
      cases u with
      | nil => cases hu
      | node c ul ur =>
        simp only [BinaryTree.map, BinaryTree.node.injEq] at hu
        obtain ⟨hc, hul, hur⟩ := hu
        refine ⟨c.2, A.run ul, A.run ur, (hl _).mpr ⟨ul, hul, rfl⟩,
          (hr _).mpr ⟨ur, hur, rfl⟩, ?_⟩
        simpa [Automaton.run, ← hc] using hq

theorem Recognizable.project {L : Set (BinaryTree (α × β))}
    (h : Recognizable L) : Recognizable {t | ∃ u ∈ L, u.map Prod.fst = t} := by
  classical
  obtain ⟨Q, hQ, A, F, hA⟩ := h
  let _ := hQ
  refine ⟨Set Q, inferInstance, A.project, {s | ∃ q ∈ s, q ∈ F}, ?_⟩
  intro t
  constructor
  · rintro ⟨u, hu, ht⟩
    exact ⟨A.run u, (A.mem_run_project t _).mpr ⟨u, ht, rfl⟩, (hA u).mp hu⟩
  · rintro ⟨q, hq, hF⟩
    obtain ⟨u, ht, hu⟩ := (A.mem_run_project t q).mp hq
    exact ⟨u, (hA u).mpr (hu ▸ hF), ht⟩

#print axioms Automaton.mem_run_project
#print axioms Recognizable.project
end StackSorting.TreeAutomaton
