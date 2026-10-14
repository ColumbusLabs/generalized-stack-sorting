import NumberedBinarySize
import FiniteTreeLogicAtoms

namespace StackSorting.FinitePort.ChildSibling
open TreeAutomaton.Logic
variable {α : Type}

theorem position_label_mem {t : BinaryTree α} (p : Position t) : p.label ∈ labels t := by
  induction p with
  | root => simp [labels, Position.label]
  | left p ih => simp only [labels, Position.label, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl ih)
  | right p ih => simp only [labels, Position.label, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr ih)

theorem mem_labels_position {t : BinaryTree α} {a : α} (h : a ∈ labels t) :
    ∃ p : Position t, p.label = a := by
  induction t with
  | nil => simp [labels] at h
  | node b l r hl hr =>
    rcases List.mem_cons.mp h with he | h
    · exact ⟨.root,he.symm⟩
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨p,hp⟩ := hl h
        exact ⟨.left p,hp⟩
      · obtain ⟨p,hp⟩ := hr h
        exact ⟨.right p,hp⟩

theorem position_label_injective {t : BinaryTree α} (h : (labels t).Nodup) :
    Function.Injective (@Position.label α t) := by
  induction t with
  | nil => intro p; cases p
  | node a l r hl hr =>
    obtain ⟨ha,hn⟩ := List.nodup_cons.mp h
    obtain ⟨hnl,hnr,hd⟩ := List.nodup_append.mp hn
    intro p q he
    cases p with
    | root =>
      cases q with
      | root => rfl
      | left q =>
        simp only [Position.label] at he
        exact False.elim (ha (List.mem_append_left _ (he.symm ▸ position_label_mem q)))
      | right q =>
        simp only [Position.label] at he
        exact False.elim (ha (List.mem_append_right _ (he.symm ▸ position_label_mem q)))
    | left p =>
      cases q with
      | root =>
        simp only [Position.label] at he
        exact False.elim (ha (List.mem_append_left _ (he ▸ position_label_mem p)))
      | left q => exact congrArg Position.left (hl hnl he)
      | right q => exact False.elim (hd _ (position_label_mem p) _ (position_label_mem q) he)
    | right p =>
      cases q with
      | root =>
        simp only [Position.label] at he
        exact False.elim (ha (List.mem_append_right _ (he ▸ position_label_mem p)))
      | left q => exact False.elim (hd _ (position_label_mem q) _ (position_label_mem p) he.symm)
      | right q => exact congrArg Position.right (hr hnr he)

/-- Literal positions in the first-child/next-sibling shape biject with
original vertices; no auxiliary nil position is introduced. -/
noncomputable def shapePositionEquiv {n} (T : RootedTree n) (O : FixedOrder n)
    (r : Fin n) (hr : r.val = 0) : Position (build T O n [r]) ≃ Fin n :=
  Equiv.ofBijective Position.label
    ⟨position_label_injective (root_shape_nodup T O r),
      fun u => mem_labels_position (root_shape_complete T O r hr u)⟩

theorem shapePositionEquiv_label {n} (T : RootedTree n) (O : FixedOrder n)
    (r : Fin n) (hr : r.val = 0) (p : Position (build T O n [r])) :
    shapePositionEquiv T O r hr p = p.label := rfl

#print axioms shapePositionEquiv
end StackSorting.FinitePort.ChildSibling
