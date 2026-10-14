import Mathlib.Data.Tree.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact finite enumeration of labeled binary trees by positive-node size.
The recursive enumeration adapts the MIT-licensed construction in mathlib's
Catalan/Tree.lean (copyright 2022 Julian Kuelshammer). Unlike the unlabelled
specialization there, every internal node here has a label from a finite type.
The unique empty tree has size zero; each constructor contributes one. -/
namespace StackSorting.TreeAutomaton
open Finset
open Finset.HasAntidiagonal.antidiagonal (fst_le snd_le)

variable {α : Type*} [Fintype α] [DecidableEq α]

def nodeTrees (a b : Finset (BinaryTree α)) : Finset (BinaryTree α) :=
  (Finset.univ ×ˢ (a ×ˢ b)).image fun p => BinaryTree.node p.1 p.2.1 p.2.2

@[simp] theorem nil_not_mem_nodeTrees (a b : Finset (BinaryTree α)) :
    BinaryTree.nil ∉ nodeTrees a b := by
  simp [nodeTrees]

@[simp] theorem node_mem_nodeTrees (c : α) (l r : BinaryTree α)
    (a b : Finset (BinaryTree α)) :
    BinaryTree.node c l r ∈ nodeTrees a b ↔ l ∈ a ∧ r ∈ b := by
  simp [nodeTrees, Prod.exists]

/-- This is an actual finset of trees, so each tree occurs once. -/
def treesOfSize : ℕ → Finset (BinaryTree α)
  | 0 => {BinaryTree.nil}
  | n + 1 => (antidiagonal n).attach.biUnion fun ij =>
      nodeTrees (treesOfSize ij.val.1) (treesOfSize ij.val.2)
  decreasing_by
    · simp_wf; have := fst_le ij.property; omega
    · simp_wf; have := snd_le ij.property; omega

@[simp] theorem treesOfSize_zero : treesOfSize (α := α) 0 = {BinaryTree.nil} := by
  rw [treesOfSize]

theorem treesOfSize_succ (n : ℕ) :
    treesOfSize (α := α) (n+1) =
      (antidiagonal n).biUnion fun ij => nodeTrees (treesOfSize ij.1) (treesOfSize ij.2) := by
  rw [treesOfSize]
  ext t
  simp

/-- Soundness and completeness for the literal tree object and its node count. -/
@[simp] theorem mem_treesOfSize (t : BinaryTree α) (n : ℕ) :
    t ∈ treesOfSize n ↔ t.numNodes = n := by
  induction t generalizing n with
  | nil => cases n <;> simp [treesOfSize_succ]
  | node c l r hl hr =>
    cases n <;> simp [treesOfSize_succ, hl, hr, Prod.exists]

/-- A deterministic bottom-up automaton. The empty tree has one specified
state; all other transitions consume exactly one positively weighted node. -/
structure Automaton (α Q : Type*) where
  emptyState : Q
  step : α → Q → Q → Q

variable {Q : Type*}

def Automaton.run (A : Automaton α Q) : BinaryTree α → Q
  | .nil => A.emptyState
  | .node c l r => A.step c (A.run l) (A.run r)

variable [DecidableEq Q]

def stateTrees (A : Automaton α Q) (q : Q) (n : ℕ) : Finset (BinaryTree α) :=
  (treesOfSize n).filter fun t => A.run t = q

@[simp] theorem mem_stateTrees (A : Automaton α Q) (q : Q) (n : ℕ)
    (t : BinaryTree α) :
    t ∈ stateTrees A q n ↔ t.numNodes = n ∧ A.run t = q := by
  simp [stateTrees]

abbrev StateSizedTree (A : Automaton α Q) (q : Q) (n : ℕ) :=
  {t : BinaryTree α // t.numNodes = n ∧ A.run t = q}

instance stateSizedTreeFintype (A : Automaton α Q) (q : Q) (n : ℕ) :
    Fintype (StateSizedTree A q n) :=
  Fintype.ofFinset (stateTrees A q n) (fun t => mem_stateTrees A q n t)

/-- Exact cardinality of distinct accepted tree objects at the stated size. -/
def treeCount (A : Automaton α Q) (q : Q) (n : ℕ) : ℕ :=
  (stateTrees A q n).card

theorem card_stateSizedTree (A : Automaton α Q) (q : Q) (n : ℕ) :
    Fintype.card (StateSizedTree A q n) = treeCount A q n := by
  exact Fintype.card_ofFinset (stateTrees A q n) (fun t => mem_stateTrees A q n t)

@[simp] theorem treeCount_zero (A : Automaton α Q) (q : Q) :
    treeCount A q 0 = if A.emptyState = q then 1 else 0 := by
  by_cases h : A.emptyState = q <;>
    simp [treeCount, stateTrees, Finset.filter_singleton, Automaton.run, h]

#print axioms mem_treesOfSize
#print axioms card_stateSizedTree
#print axioms treeCount_zero
end StackSorting.TreeAutomaton
