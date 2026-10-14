import OrderedNumberedChildren
import Mathlib.Data.Tree.Basic

namespace StackSorting.FinitePort.ChildSibling
variable {n : Nat} (T : RootedTree n) (O : FixedOrder n)

/-- Fuel bounds tree depth; list recursion builds next siblings. Nil carries
no label and contributes no counted vertex. -/
def build : Nat → List (Fin n) → BinaryTree (Fin n)
  | 0, _ => .nil
  | _+1, [] => .nil
  | fuel+1, v::vs => .node v (build fuel (children T O v)) (build (fuel+1) vs)

def labels {α : Type} : BinaryTree α → List α
  | .nil => []
  | .node a l r => a :: (labels l ++ labels r)

@[simp] theorem build_nil (fuel : Nat) : build T O fuel [] = .nil := by
  cases fuel <;> simp only [build]

theorem child_fuel {fuel : Nat} {v w : Fin n}
    (hv : n-v.val ≤ fuel+1) (hw : w ∈ children T O v) : n-w.val ≤ fuel := by
  have h := child_gt T O hw
  have hh := w.isLt
  omega

theorem mem_build_labels (fuel : Nat) (xs : List (Fin n))
    (hf : ∀ v ∈ xs, n-v.val ≤ fuel) (u : Fin n) :
    u ∈ labels (build T O fuel xs) ↔ ∃ v ∈ xs, Ancestor T v u := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro v hv
      have h := hf v hv
      have hi := v.isLt
      omega
    subst xs
    simp [labels]
  | succ fuel ih =>
    induction xs with
    | nil => simp [labels]
    | cons v vs ht =>
      have hv := hf v (by simp)
      have hf' : ∀ w ∈ vs, n-w.val ≤ fuel+1 := fun w hw => hf w (by simp [hw])
      have hch : ∀ w ∈ children T O v, n-w.val ≤ fuel := fun _ hw => child_fuel T O hv hw
      rw [build, labels, List.mem_cons, List.mem_append, ih _ hch, ht hf']
      constructor
      · rintro (he | ⟨w,hw,ha⟩ | ⟨w,hw,ha⟩)
        · subst u
          exact ⟨v,by simp,Ancestor.refl v⟩
        · exact ⟨v,by simp,(child_ancestor T O hw).trans ha⟩
        · exact ⟨w,by simp [hw],ha⟩
      · rintro ⟨w,hw,ha⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · rcases (ancestor_child_split T O).mp ha with he | hh
          · exact Or.inl he
          · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr ⟨w,hw,ha⟩)

/-- The root shape contains every original vertex, at positive-node positions. -/
theorem root_shape_complete (r : Fin n) (hr : r.val = 0) (u : Fin n) :
    u ∈ labels (build T O n [r]) := by
  apply (mem_build_labels T O n [r] (by intro v hv; omega) u).mpr
  exact ⟨r,by simp,root_ancestor T r hr u⟩

#print axioms mem_build_labels
#print axioms root_shape_complete
end StackSorting.FinitePort.ChildSibling
