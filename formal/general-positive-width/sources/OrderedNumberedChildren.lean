import DecompositionIntroduction

namespace StackSorting.FinitePort.ChildSibling
open GraphWidth

variable {n : Nat} (T : RootedTree n) (O : FixedOrder n)

def children (v : Fin n) : List (Fin n) :=
  O.vertices.filter (fun w => decide (w.val ≠ 0 ∧ T.parent w = v))

@[simp] theorem mem_children (v w : Fin n) :
    w ∈ children T O v ↔ w.val ≠ 0 ∧ T.parent w = v := by
  simp [children, O.complete]

theorem children_nodup (v : Fin n) : (children T O v).Nodup := O.nodup.filter _

theorem child_gt {v w : Fin n} (h : w ∈ children T O v) : v.val < w.val := by
  obtain ⟨hz,hp⟩ := (mem_children T O v w).mp h
  simpa only [hp] using T.parent_lt w hz

theorem child_ancestor {v w : Fin n} (h : w ∈ children T O v) : Ancestor T v w := by
  obtain ⟨hz,hp⟩ := (mem_children T O v w).mp h
  apply Ancestor.step hz
  rw [hp]
  exact .refl _

/-- Immediate children partition the strict descendants. -/
theorem ancestor_child_split {v u : Fin n} :
    Ancestor T v u ↔ u = v ∨ ∃ w ∈ children T O v, Ancestor T w u := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @step u hz hp ih =>
      rcases ih with he | ⟨w,hw,ha⟩
      · exact Or.inr ⟨u, (mem_children T O v u).mpr ⟨hz,he⟩, .refl _⟩
      · exact Or.inr ⟨w,hw,.step hz ha⟩
  · rintro (rfl | ⟨w,hw,ha⟩)
    · exact .refl _
    · exact (child_ancestor T O hw).trans ha

theorem children_incomparable {v a b : Fin n}
    (ha : a ∈ children T O v) (hb : b ∈ children T O v)
    (h : Ancestor T a b) : a = b := by
  by_contra he
  have hp := h.parent_of_ne he
  have hbpar := ((mem_children T O v b).mp hb).2
  rw [hbpar] at hp
  have hx := hp.val_le
  have hy := child_gt T O ha
  omega

theorem children_descendants_disjoint {v a b u : Fin n}
    (ha : a ∈ children T O v) (hb : b ∈ children T O v)
    (hau : Ancestor T a u) (hbu : Ancestor T b u) : a = b := by
  rcases TreeAncestry.comparable hau hbu with h | h
  · exact children_incomparable T O ha hb h
  · exact (children_incomparable T O hb ha h).symm

theorem root_ancestor (r : Fin n) (hr : r.val = 0) (v : Fin n) : Ancestor T r v := by
  by_cases hv : v.val = 0
  · have he : r = v := Fin.ext (hr.trans hv.symm)
    subst v
    exact .refl _
  · exact .step hv (root_ancestor r hr (T.parent v))
termination_by v.val
decreasing_by exact T.parent_lt v hv

#print axioms ancestor_child_split
#print axioms children_descendants_disjoint
end StackSorting.FinitePort.ChildSibling
