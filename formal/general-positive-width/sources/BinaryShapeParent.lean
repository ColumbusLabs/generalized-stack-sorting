import NumberedBinarySize

namespace StackSorting.FinitePort.ChildSibling
variable {n : Nat} (T : RootedTree n) (O : FixedOrder n)

/-- Follow next-sibling pointers only. -/
def rootLabels {α : Type} : BinaryTree α → List α
  | .nil => []
  | .node a _ r => a :: rootLabels r

/-- Parent means one first-child pointer and then zero or more sibling
pointers. This recursive witness ignores relation labels completely. -/
def ParentWitness {α : Type} : BinaryTree α → α → α → Prop
  | .nil, _, _ => False
  | .node a l r, u, v => (u = a ∧ v ∈ rootLabels l) ∨ ParentWitness l u v ∨ ParentWitness r u v

theorem rootLabels_build (fuel : Nat) (xs : List (Fin n))
    (hf : ∀ v ∈ xs, n-v.val ≤ fuel) : rootLabels (build T O fuel xs) = xs := by
  cases fuel with
  | zero =>
    have he : xs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro v hv
      have h := hf v hv
      have hi := v.isLt
      omega
    subst xs
    simp [rootLabels]
  | succ fuel =>
    induction xs with
    | nil => simp [rootLabels]
    | cons v vs ih =>
      rw [build,rootLabels,ih (fun w hw => hf w (by simp [hw]))]

theorem parentWitness_build (fuel : Nat) (xs : List (Fin n))
    (hf : ∀ w ∈ xs, n-w.val ≤ fuel) (u v : Fin n) :
    ParentWitness (build T O fuel xs) u v ↔
      (∃ a ∈ xs, Ancestor T a u) ∧ v ∈ children T O u := by
  induction fuel generalizing xs with
  | zero =>
    have he : xs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro w hw
      have h := hf w hw
      have hi := w.isLt
      omega
    subst xs
    simp [ParentWitness]
  | succ fuel ih =>
    induction xs with
    | nil => simp [ParentWitness]
    | cons a rest ht =>
      have hch : ∀ w ∈ children T O a, n-w.val ≤ fuel :=
        fun _ hw => child_fuel T O (hf a (by simp)) hw
      have hrest : ∀ w ∈ rest, n-w.val ≤ fuel+1 := fun w hw => hf w (by simp [hw])
      rw [build, ParentWitness, rootLabels_build T O fuel _ hch, ih _ hch, ht hrest]
      constructor
      · rintro (⟨rfl,hv⟩ | ⟨⟨w,hw,hwu⟩,hv⟩ | ⟨⟨w,hw,hwu⟩,hv⟩)
        · exact ⟨⟨u,by simp,.refl _⟩,hv⟩
        · exact ⟨⟨a,by simp,(child_ancestor T O hw).trans hwu⟩,hv⟩
        · exact ⟨⟨w,by simp [hw],hwu⟩,hv⟩
      · rintro ⟨⟨w,hw,hwu⟩,hv⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · rcases (ancestor_child_split T O).mp hwu with he | hd
          · subst u; exact Or.inl ⟨rfl,hv⟩
          · exact Or.inr (Or.inl ⟨hd,hv⟩)
        · exact Or.inr (Or.inr ⟨⟨w,hw,hwu⟩,hv⟩)

/-- Exact original parent recovery in the constructed binary shape. -/
theorem root_shape_parent (r : Fin n) (hr : r.val = 0) (u v : Fin n) :
    ParentWitness (build T O n [r]) u v ↔ v.val ≠ 0 ∧ T.parent v = u := by
  rw [parentWitness_build T O n [r] (fun _ _ => Nat.sub_le _ _) u v, mem_children]
  constructor
  · exact And.right
  · intro hv
    exact ⟨⟨r,by simp,root_ancestor T r hr u⟩,hv⟩

#print axioms root_shape_parent
end StackSorting.FinitePort.ChildSibling
