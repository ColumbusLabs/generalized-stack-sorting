import BinaryShapePositions
import FiniteTreePositionSemantics

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α β : Type}

/-- Relabelling preserves addresses even when vertex labels are not injective. -/
def mapPosition (f : α → β) : {t : BinaryTree α} → Position t → Position (t.map f)
  | .node _ _ _, .root => .root
  | .node _ _ _, .left p => .left (mapPosition f p)
  | .node _ _ _, .right p => .right (mapPosition f p)

def unmapPosition (f : α → β) : (t : BinaryTree α) → Position (t.map f) → Position t
  | .nil, p => nomatch p
  | .node _ _ _, .root => .root
  | .node _ l _, .left p => .left (unmapPosition f l p)
  | .node _ _ r, .right p => .right (unmapPosition f r p)

@[simp] theorem unmap_mapPosition (f : α → β) {t : BinaryTree α} (p : Position t) :
    unmapPosition f t (mapPosition f p) = p := by
  induction p with
  | root => rfl
  | left p ih => exact congrArg Position.left ih
  | right p ih => exact congrArg Position.right ih

@[simp] theorem map_unmapPosition (f : α → β) (t : BinaryTree α) (p : Position (t.map f)) :
    mapPosition f (unmapPosition f t p) = p := by
  induction t with
  | nil => cases p
  | node a l r hl hr =>
    cases p with
    | root => rfl
    | left p => exact congrArg Position.left (hl p)
    | right p => exact congrArg Position.right (hr p)

def positionMapEquiv (f : α → β) (t : BinaryTree α) : Position t ≃ Position (t.map f) where
  toFun := mapPosition f
  invFun := unmapPosition f t
  left_inv := unmap_mapPosition f
  right_inv := map_unmapPosition f t

@[simp] theorem mapPosition_label (f : α → β) {t : BinaryTree α} (p : Position t) :
    (mapPosition f p).label = f p.label := by
  induction p with
  | root => rfl
  | left p ih => exact ih
  | right p ih => exact ih

theorem unmapPosition_label (f : α → β) (t : BinaryTree α) (p : Position (t.map f)) :
    f (unmapPosition f t p).label = p.label := by
  have h := mapPosition_label f (unmapPosition f t p)
  rw [map_unmapPosition] at h
  exact h.symm

theorem child_mapPosition (f : α → β) {t : BinaryTree α} {d : Bool} {p q : Position t}
    (h : Child d p q) : Child d (mapPosition f p) (mapPosition f q) := by
  induction h with
  | rootLeft => exact .rootLeft
  | rootRight => exact .rootRight
  | left h ih => exact .left ih
  | right h ih => exact .right ih

theorem child_unmapPosition (f : α → β) (t : BinaryTree α)
    {d : Bool} {p q : Position (t.map f)} (h : Child d p q) :
    Child d (unmapPosition f t p) (unmapPosition f t q) := by
  induction t with
  | nil => cases p
  | node a l r hl hr =>
    cases l <;> cases r <;> cases h
    all_goals first
      | exact Child.rootLeft
      | exact Child.rootRight
      | (apply Child.left; apply hl; assumption)
      | (apply Child.right; apply hr; assumption)

theorem child_positionMapEquiv (f : α → β) (t : BinaryTree α)
    {d : Bool} {p q : Position t} :
    Child d (positionMapEquiv f t p) (positionMapEquiv f t q) ↔ Child d p q := by
  constructor
  · intro h
    simpa only [positionMapEquiv, Equiv.coe_fn_mk, unmap_mapPosition] using
      child_unmapPosition f t h
  · exact child_mapPosition f

#print axioms positionMapEquiv
#print axioms child_positionMapEquiv
end StackSorting.FinitePort.ChildSibling
