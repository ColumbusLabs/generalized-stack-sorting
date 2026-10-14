import SubstitutionWalks
import DecompositionIntroduction

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.GraphWidth.Nested.TreeSubstitution
open FinitePort
variable {t : Nat} {T : RootedTree t} (S : TreeSubstitution T)

/-- Local ancestor chains embed as actual directed union-tree chains. -/
theorem local_ancestor (x : Fin t) {a b : Fin (S.size x)}
    (h : Ancestor (S.localTree x) a b) :
    Ancestor S.tree (S.index ⟨x,a⟩) (S.index ⟨x,b⟩) := by
  induction h with
  | refl => exact .refl _
  | @step b hb h ih =>
    have hn : (S.index ⟨x,b⟩).val ≠ 0 := by
      intro hz
      have he := (S.index_zero_iff ⟨x,b⟩).mp hz
      have hval := congrArg (fun a : S.Node => a.2.val) he
      exact hb hval
    apply Ancestor.step hn
    rw [S.parent_index]
    simpa [parent,hb] using ih

/-- Every local vertex descends from its own marginal root. -/
theorem localRoot_ancestor (a : S.Node) :
    Ancestor S.tree (S.index (S.localRoot a.1)) (S.index a) := by
  apply S.local_ancestor a.1
  apply TreeAncestry.ancestor_of_walk_minimum (tree_connected (S.localTree a.1) ⟨0,S.positive _⟩ a.2)
    (fun _ _ => Nat.zero_le _) (.refl _)

theorem parent_outer_ancestor (a : S.Node) : Ancestor T (S.parent a).1 a.1 := by
  unfold parent
  split_ifs with hi hx
  · exact .refl _
  · exact .step hx (.refl _)
  · exact .refl _

/-- Projection of union-tree ancestry is genuine outer-tree ancestry. -/
theorem ancestor_outer {a b : Fin (Fintype.card S.Node)}
    (h : Ancestor S.tree a b) : Ancestor T (S.label a).1 (S.label b).1 := by
  induction h with
  | refl => exact .refl _
  | @step b hb h ih =>
    rw [S.exact_parent] at ih
    exact ih.trans (S.parent_outer_ancestor _)

theorem outer_ancestor_localRoot {x y : Fin t} (h : Ancestor T x y) :
    Ancestor S.tree (S.index (S.localRoot x)) (S.index (S.localRoot y)) := by
  induction h with
  | refl => exact .refl _
  | @step y hy h ih =>
    have hp := S.localRoot_ancestor ⟨T.parent y,S.attachment y⟩
    have hq := ih.trans hp
    have hn : (S.index (S.localRoot y)).val ≠ 0 := by
      intro hz
      have he := (S.index_zero_iff (S.localRoot y)).mp hz
      exact hy (congrArg (fun a : S.Node => a.1.val) he)
    apply Ancestor.step hn
    rw [S.parent_index,S.parent_localRoot y hy]
    exact hq

/-- The entire component under an outer node is exactly the union-tree
subtree rooted at that node's incoming marginal endpoint. -/
theorem outer_ancestor_iff (x : Fin t) (a : S.Node) :
    Ancestor T x a.1 ↔ Ancestor S.tree (S.index (S.localRoot x)) (S.index a) := by
  constructor
  · intro h
    exact (S.outer_ancestor_localRoot h).trans (S.localRoot_ancestor a)
  · intro h
    have hp := S.ancestor_outer h
    simpa only [S.label_index,localRoot] using hp

#print axioms local_ancestor
#print axioms ancestor_outer
#print axioms outer_ancestor_iff
end StackSorting.GraphWidth.Nested.TreeSubstitution
