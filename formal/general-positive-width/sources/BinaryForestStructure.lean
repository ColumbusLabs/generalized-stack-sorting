import BinaryParentPositions

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type}

/-- The actual preorder index of a binary position, independent of labels. -/
def positionRank : {t : BinaryTree α} → Position t → Nat
  | .node _ _ _, .root => 0
  | .node _ _ _, .left p => 1 + positionRank p
  | .node _ l _, .right p => 1 + l.numNodes + positionRank p

theorem positionRank_lt {t : BinaryTree α} (p : Position t) :
    positionRank p < t.numNodes := by
  induction p with
  | root => simp only [positionRank,BinaryTree.numNodes]; omega
  | left p ih => simp only [positionRank,BinaryTree.numNodes]; omega
  | right p ih => simp only [positionRank,BinaryTree.numNodes]; omega

theorem parentPosition_rank_lt {t : BinaryTree α} {p q : Position t}
    (h : ParentPosition p q) : positionRank p < positionRank q := by
  induction h with
  | root _ => simp only [positionRank]; omega
  | left _ ih => simp only [positionRank]; omega
  | right _ ih => simp only [positionRank]; omega

theorem rootSibling_no_parent {t : BinaryTree α} {q : Position t}
    (hq : RootSibling q) {p : Position t} : ¬ ParentPosition p q := by
  induction hq with
  | root => intro h; cases h
  | right h ih => intro hp; cases hp with | right hp => exact ih hp

theorem parentPosition_unique {t : BinaryTree α} {p q : Position t}
    (h : ParentPosition p q) {p' : Position t} (h' : ParentPosition p' q) : p=p' := by
  induction h with
  | root hr =>
    cases h' with
    | root _ => rfl
    | left hp => exact False.elim (rootSibling_no_parent hr hp)
  | left hp ih =>
    cases h' with
    | root hr => exact False.elim (rootSibling_no_parent hr hp)
    | left hq => exact congrArg Position.left (ih hq)
  | right hp ih =>
    cases h' with
    | right hq => exact congrArg Position.right (ih hq)

theorem position_root_or_parent {t : BinaryTree α} (q : Position t) :
    RootSibling q ∨ ∃ p, ParentPosition p q := by
  induction q with
  | root => exact Or.inl .root
  | left q ih =>
    rcases ih with hr | ⟨p,hp⟩
    · exact Or.inr ⟨.root,.root hr⟩
    · exact Or.inr ⟨.left p,.left hp⟩
  | right q ih =>
    rcases ih with hr | ⟨p,hp⟩
    · exact Or.inl (.right hr)
    · exact Or.inr ⟨.right p,.right hp⟩

/-- The roots of the represented forest are exactly the positions with no
original parent. This handles nil and arbitrary repeated labels. -/
theorem rootSibling_iff_no_parent {t : BinaryTree α} (q : Position t) :
    RootSibling q ↔ ¬ ∃ p, ParentPosition p q := by
  constructor
  · rintro hr ⟨p,hp⟩
    exact rootSibling_no_parent hr hp
  · intro h
    rcases position_root_or_parent q with hr | hp
    · exact hr
    · exact False.elim (h hp)

/-- A normalized nonempty binary code is an actual single rooted tree: each
position other than its root has exactly one original parent. -/
theorem normal_position_unique_parent (a : α) (l : BinaryTree α)
    (q : Position (.node a l .nil)) (hq : q ≠ .root) :
    ∃! p, ParentPosition p q := by
  rcases position_root_or_parent q with hr | ⟨p,hp⟩
  · cases hr with
    | root => exact False.elim (hq rfl)
    | right h => cases h
  · exact ⟨p,hp,fun _ h => parentPosition_unique h hp⟩

#print axioms parentPosition_unique
#print axioms normal_position_unique_parent
end StackSorting.FinitePort.ChildSibling
