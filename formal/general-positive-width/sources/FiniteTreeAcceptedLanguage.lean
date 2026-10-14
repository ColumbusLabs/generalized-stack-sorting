import FiniteTreeRootBijection

/-! Accepting-state unions preserve one count per actual tree. -/
namespace StackSorting.TreeAutomaton
open Finset
variable {α Q : Type*} [Fintype α] [DecidableEq α] [DecidableEq Q]

def acceptedTrees (A : Automaton α Q) (accept : Finset Q) (n : ℕ) :
    Finset (BinaryTree α) :=
  (treesOfSize n).filter fun t => A.run t ∈ accept

@[simp] theorem mem_acceptedTrees (A : Automaton α Q) (accept : Finset Q)
    (n : ℕ) (t : BinaryTree α) :
    t ∈ acceptedTrees A accept n ↔ t.numNodes = n ∧ A.run t ∈ accept := by
  simp [acceptedTrees]

theorem acceptedTrees_eq_union (A : Automaton α Q) (accept : Finset Q) (n : ℕ) :
    acceptedTrees A accept n = accept.biUnion fun q => stateTrees A q n := by
  ext t
  simp [mem_acceptedTrees, and_left_comm]

theorem distinct_states_disjoint (A : Automaton α Q) (n : ℕ) {q r : Q}
    (h : q ≠ r) : Disjoint (stateTrees A q n) (stateTrees A r n) := by
  rw [Finset.disjoint_left]
  intro t ht hr
  exact h (((mem_stateTrees A q n t).mp ht).2.symm.trans
    ((mem_stateTrees A r n t).mp hr).2)

/-- This coefficient counts trees, not witnesses of accepting runs. -/
theorem acceptedTrees_card (A : Automaton α Q) (accept : Finset Q) (n : ℕ) :
    (acceptedTrees A accept n).card = ∑ q ∈ accept, treeCount A q n := by
  rw [acceptedTrees_eq_union, Finset.card_biUnion]
  · rfl
  · intro q hq r hr hne
    exact distinct_states_disjoint A n hne

#print axioms mem_acceptedTrees
#print axioms acceptedTrees_card
end StackSorting.TreeAutomaton
