import BinaryPositionNumbering

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type}

/-- A normalized nonempty binary tree determines its original parent function.
The dummy parent of the root is fixed to the root only by this construction. -/
noncomputable def normalPositionParent (a : α) (l : BinaryTree α)
    (q : Position (.node a l .nil)) : Position (.node a l .nil) := by
  classical
  exact if h : q=.root then .root else
    Classical.choose (normal_position_unique_parent a l q h)

theorem normalPositionParent_spec (a : α) (l : BinaryTree α)
    (q : Position (.node a l .nil)) (hq : q≠.root) :
    ParentPosition (normalPositionParent a l q) q := by
  classical
  simp only [normalPositionParent,dite_eq_right hq]
  exact (Classical.choose_spec (normal_position_unique_parent a l q hq)).1

theorem normalPositionParent_root (a : α) (l : BinaryTree α) :
    normalPositionParent a l .root=.root := by
  classical
  simp [normalPositionParent]

/-- Exact reverse reconstruction on the actual number of binary positions;
no extra root or nil vertex is introduced. -/
noncomputable def normalPositionTree (a : α) (l : BinaryTree α) :
    RootedTree (BinaryTree.node a l .nil).numNodes where
  parent i := positionIndexEquiv _ (normalPositionParent a l ((positionIndexEquiv _).symm i))
  parent_lt i hi := by
    let q := (positionIndexEquiv (.node a l .nil)).symm i
    have hq : q≠.root := by
      intro he
      have hz : (positionIndexEquiv (.node a l .nil) q).val=0 := by rw [he]; rfl
      have heq : positionIndexEquiv (.node a l .nil) q=i := Equiv.apply_symm_apply _ _
      rw [heq] at hz
      exact hi hz
    have hlt := parentPosition_rank_lt (normalPositionParent_spec a l q hq)
    change positionRank (normalPositionParent a l q)<i.val
    have heq : positionIndexEquiv (.node a l .nil) q=i := Equiv.apply_symm_apply _ _
    have hr : positionRank q=i.val := congrArg Fin.val heq
    rwa [hr] at hlt

theorem normalPositionTree_exact_parent (a : α) (l : BinaryTree α)
    (p q : Position (.node a l .nil)) :
    ((positionIndexEquiv _ q).val≠0 ∧
      (normalPositionTree a l).parent (positionIndexEquiv _ q)=positionIndexEquiv _ p) ↔
    ParentPosition p q := by
  constructor
  · rintro ⟨hn,hp⟩
    have hq : q≠.root := by intro he; subst q; exact hn rfl
    have he : normalPositionParent a l q=p := by
      apply (positionIndexEquiv _).injective
      simpa only [normalPositionTree,Equiv.symm_apply_apply] using hp
    rw [←he]
    exact normalPositionParent_spec a l q hq
  · intro h
    have hq : q≠.root := by
      intro he
      subst q
      exact rootSibling_no_parent RootSibling.root h
    constructor
    · intro hz
      exact hq ((positionRank_zero_iff a l .nil q).mp hz)
    · have he : normalPositionParent a l q=p :=
        parentPosition_unique (normalPositionParent_spec a l q hq) h
      simp only [normalPositionTree,Equiv.symm_apply_apply,he]

#print axioms normalPositionTree
#print axioms normalPositionTree_exact_parent
end StackSorting.FinitePort.ChildSibling
