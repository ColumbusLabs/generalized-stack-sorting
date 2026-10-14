import BinaryNormalTree

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α β γ : Type}

/-- The ordered literal positions along a forest's root sibling chain. -/
def positionRoots : (t : BinaryTree α) → List (Position t)
  | .nil => []
  | .node _ _ r => .root :: (positionRoots r).map Position.right

/-- The ordered literal positions of the children of a node. -/
def positionChildren : {t : BinaryTree α} → Position t → List (Position t)
  | .node _ l _, .root => (positionRoots l).map Position.left
  | .node _ _ _, .left p => (positionChildren p).map Position.left
  | .node _ _ _, .right p => (positionChildren p).map Position.right

@[simp] theorem mem_positionRoots {t : BinaryTree α} (p : Position t) :
    p ∈ positionRoots t ↔ RootSibling p := by
  induction t with
  | nil => cases p
  | node a l r ihl ihr =>
    cases p with
    | root => simp [positionRoots]; exact RootSibling.root
    | left p =>
      constructor
      · simp [positionRoots]
      · intro h; cases h
    | right p =>
      constructor
      · intro h
        have hp : p ∈ positionRoots r := by simpa [positionRoots] using h
        exact .right ((ihr p).mp hp)
      · intro h
        cases h with
        | right h => simpa [positionRoots] using (ihr p).mpr h

@[simp] theorem mem_positionChildren {t : BinaryTree α} (p q : Position t) :
    q ∈ positionChildren p ↔ ParentPosition p q := by
  induction p with
  | root =>
    cases q with
    | root =>
      constructor
      · simp [positionChildren]
      · intro h; cases h
    | left q =>
      constructor
      · intro h
        exact .root ((mem_positionRoots q).mp (by simpa [positionChildren] using h))
      · intro h
        cases h with
        | root h => simpa [positionChildren] using (mem_positionRoots q).mpr h
    | right q =>
      constructor
      · simp [positionChildren]
      · intro h; cases h
  | left p ih =>
    cases q with
    | root =>
      constructor
      · simp [positionChildren]
      · intro h; cases h
    | left q =>
      constructor
      · intro h; exact .left ((ih q).mp (by simpa [positionChildren] using h))
      · intro h; cases h with | left h => simpa [positionChildren] using (ih q).mpr h
    | right q =>
      constructor
      · simp [positionChildren]
      · intro h; cases h
  | right p ih =>
    cases q with
    | root =>
      constructor
      · simp [positionChildren]
      · intro h; cases h
    | left q =>
      constructor
      · simp [positionChildren]
      · intro h; cases h
    | right q =>
      constructor
      · intro h; exact .right ((ih q).mp (by simpa [positionChildren] using h))
      · intro h; cases h with | right h => simpa [positionChildren] using (ih q).mpr h

/-- Label each node by a function of its literal position. Unlike ordinary
map, this can distinguish nodes that initially carry colliding labels. -/
def positionRelabel : (t : BinaryTree α) → (Position t → β) → BinaryTree β
  | .nil, _ => .nil
  | .node _ l r, f => .node (f .root)
      (positionRelabel l (fun p => f (.left p)))
      (positionRelabel r (fun p => f (.right p)))

@[simp] theorem positionRelabel_labels (t : BinaryTree α) :
    positionRelabel t Position.label = t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr => simpa only [positionRelabel, Position.label] using congrArg₂ (BinaryTree.node a) ihl ihr

theorem positionRelabel_map (t : BinaryTree α) (f : Position t → β) (g : β → γ) :
    (positionRelabel t f).map g = positionRelabel t (fun p => g (f p)) := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr => simp only [positionRelabel, BinaryTree.map, ihl, ihr]

theorem rootLabels_positionRelabel (t : BinaryTree α) (f : Position t → β) :
    rootLabels (positionRelabel t f) = (positionRoots t).map f := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr => simp only [positionRelabel, rootLabels, positionRoots,
      List.map_cons, List.map_map, Function.comp_def, ihr]

#print axioms mem_positionRoots
#print axioms mem_positionChildren
#print axioms positionRelabel_map
end StackSorting.FinitePort.ChildSibling
