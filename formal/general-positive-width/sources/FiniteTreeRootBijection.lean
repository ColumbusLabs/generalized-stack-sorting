import FiniteLabelledTreeEnumeration
import Mathlib.Data.Fintype.BigOperators

/-! A two-sided root-decomposition bijection for actual accepted tree objects.
The child states are recovered by deterministic evaluation, not chosen runs. -/
namespace StackSorting.TreeAutomaton
open Finset

variable {α Q : Type*} [Fintype α] [DecidableEq α] [Fintype Q] [DecidableEq Q]

abbrev Production (A : Automaton α Q) (q : Q) :=
  {p : α × Q × Q // A.step p.1 p.2.1 p.2.2 = q}

abbrev SizeSplit (n : ℕ) := ↥(Finset.antidiagonal n)

abbrev RootChoice (A : Automaton α Q) (q : Q) (n : ℕ) :=
  Σ ij : SizeSplit n, Σ p : Production A q,
    StateSizedTree A p.val.2.1 ij.val.1 × StateSizedTree A p.val.2.2 ij.val.2

/-- Unique decomposition records the actual label, child sizes and child states. -/
def splitRoot (A : Automaton α Q) (q : Q) (n : ℕ)
    (t : StateSizedTree A q (n+1)) : RootChoice A q n := by
  rcases t with ⟨t, h⟩
  cases t with
  | nil => simp at h
  | node c l r =>
    refine ⟨⟨(l.numNodes, r.numNodes), ?_⟩,
      ⟨(c, A.run l, A.run r), h.2⟩,
      ⟨⟨l, rfl, rfl⟩, ⟨r, rfl, rfl⟩⟩⟩
    simpa using h.1

/-- Reconstruction consumes one node, so recursive children are strictly smaller. -/
def joinRoot (A : Automaton α Q) (q : Q) (n : ℕ)
    (c : RootChoice A q n) : StateSizedTree A q (n+1) := by
  rcases c with ⟨ij, p, l, r⟩
  refine ⟨.node p.val.1 l.val r.val, ?_, ?_⟩
  · have hij := Finset.mem_antidiagonal.mp ij.property
    simp only [BinaryTree.numNodes, l.property.1, r.property.1]
    omega
  · change A.step p.val.1 (A.run l.val) (A.run r.val) = q
    rw [l.property.2, r.property.2]
    exact p.property

omit [Fintype α] [DecidableEq α] [Fintype Q] [DecidableEq Q] in
theorem join_splitRoot (A : Automaton α Q) (q : Q) (n : ℕ)
    (t : StateSizedTree A q (n+1)) : joinRoot A q n (splitRoot A q n t) = t := by
  rcases t with ⟨t, ht, hs⟩
  apply Subtype.ext
  cases t with
  | nil => simp at ht
  | node c l r => rfl

omit [Fintype α] [DecidableEq α] [Fintype Q] [DecidableEq Q] in
theorem split_joinRoot (A : Automaton α Q) (q : Q) (n : ℕ)
    (c : RootChoice A q n) : splitRoot A q n (joinRoot A q n c) = c := by
  rcases c with ⟨⟨⟨i,j⟩, hij⟩, ⟨⟨a,ql,qr⟩, hp⟩, ⟨⟨l,hl,sl⟩,⟨r,hr,sr⟩⟩⟩
  cases hl
  cases hr
  cases sl
  cases sr
  simp [splitRoot, joinRoot]

/-- The counting decomposition is bijective, so it does not count parse witnesses. -/
def rootEquiv (A : Automaton α Q) (q : Q) (n : ℕ) :
    StateSizedTree A q (n+1) ≃ RootChoice A q n where
  toFun := splitRoot A q n
  invFun := joinRoot A q n
  left_inv := join_splitRoot A q n
  right_inv := split_joinRoot A q n

/-- The exact finite-state convolution recurrence, derived from actual trees. -/
theorem treeCount_succ (A : Automaton α Q) (q : Q) (n : ℕ) :
    treeCount A q (n+1) =
      ∑ ij : SizeSplit n, ∑ p : Production A q,
        treeCount A p.val.2.1 ij.val.1 * treeCount A p.val.2.2 ij.val.2 := by
  rw [← card_stateSizedTree, Fintype.card_congr (rootEquiv A q n)]
  simp only [RootChoice, Fintype.card_sigma, Fintype.card_prod, card_stateSizedTree]

#print axioms rootEquiv
#print axioms treeCount_succ
end StackSorting.TreeAutomaton
