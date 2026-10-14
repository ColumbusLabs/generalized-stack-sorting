import BinaryPositionRelabeling
import BinaryShapeParent

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type}

/-- Positions encountered by following only the next-sibling pointers from
the current forest's first root. -/
inductive RootSibling : {t : BinaryTree α} → Position t → Prop
  | root {a l r} : RootSibling (t := .node a l r) .root
  | right {a l r} {p : Position r} (h : RootSibling p) :
      RootSibling (t := .node a l r) (.right p)

/-- The ordered unranked parent relation represented by the binary shape.
The root case uses one first-child pointer and an arbitrary sibling suffix. -/
inductive ParentPosition : {t : BinaryTree α} → Position t → Position t → Prop
  | root {a l r} {p : Position l} (h : RootSibling p) :
      ParentPosition (t := .node a l r) .root (.left p)
  | left {a l r} {p q : Position l} (h : ParentPosition p q) :
      ParentPosition (t := .node a l r) (.left p) (.left q)
  | right {a l r} {p q : Position r} (h : ParentPosition p q) :
      ParentPosition (t := .node a l r) (.right p) (.right q)

theorem rootSibling_label {t : BinaryTree α} {p : Position t} (h : RootSibling p) :
    p.label ∈ rootLabels t := by
  induction h with
  | root => simp [rootLabels,Position.label]
  | right h ih => simp [rootLabels,Position.label,ih]

theorem rootLabels_position {t : BinaryTree α} {a : α} (h : a ∈ rootLabels t) :
    ∃ p : Position t, RootSibling p ∧ p.label = a := by
  induction t with
  | nil => simp [rootLabels] at h
  | node b l r _ hr =>
    rcases List.mem_cons.mp h with he | h
    · exact ⟨.root,.root,he.symm⟩
    · obtain ⟨p,hp,ha⟩ := hr h
      exact ⟨.right p,.right hp,ha⟩

theorem parentPosition_labels {t : BinaryTree α} {p q : Position t}
    (h : ParentPosition p q) : ParentWitness t p.label q.label := by
  induction h with
  | root h => exact Or.inl ⟨rfl,rootSibling_label h⟩
  | left h ih => exact Or.inr (Or.inl ih)
  | right h ih => exact Or.inr (Or.inr ih)

theorem parentWitness_positions {t : BinaryTree α} {a b : α}
    (h : ParentWitness t a b) :
    ∃ p q : Position t, ParentPosition p q ∧ p.label = a ∧ q.label = b := by
  induction t with
  | nil => exact False.elim h
  | node c l r hl hr =>
    rcases h with ⟨ha,hb⟩ | h | h
    · obtain ⟨q,hq,hb⟩ := rootLabels_position hb
      exact ⟨.root,.left q,.root hq,ha.symm,hb⟩
    · obtain ⟨p,q,hpq,hp,hq⟩ := hl h
      exact ⟨.left p,.left q,.left hpq,hp,hq⟩
    · obtain ⟨p,q,hpq,hp,hq⟩ := hr h
      exact ⟨.right p,.right q,.right hpq,hp,hq⟩

theorem parentPosition_iff_labels {t : BinaryTree α} (hn : (labels t).Nodup)
    (p q : Position t) : ParentPosition p q ↔ ParentWitness t p.label q.label := by
  constructor
  · exact parentPosition_labels
  · intro h
    obtain ⟨u,v,hp,hu,hv⟩ := parentWitness_positions h
    have hi := position_label_injective hn
    have heu := hi hu
    have hev := hi hv
    subst u; subst v
    exact hp

/-- Actual positions recover exactly the original parent, with the root
having no parent despite its dummy root-pointer convention. -/
theorem original_parent_position {n} (T : RootedTree n) (O : FixedOrder n)
    (r : Fin n) (hr : r.val = 0) (p q : Position (build T O n [r])) :
    ParentPosition p q ↔ q.label.val ≠ 0 ∧ T.parent q.label = p.label := by
  rw [parentPosition_iff_labels (root_shape_nodup T O r), root_shape_parent T O r hr]

#print axioms original_parent_position
end StackSorting.FinitePort.ChildSibling
