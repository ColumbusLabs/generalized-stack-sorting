import NumberedBinaryShape
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

namespace StackSorting.FinitePort.ChildSibling
open GraphWidth
variable {n : Nat} (T : RootedTree n) (O : FixedOrder n)

def RootAntichain (xs : List (Fin n)) : Prop :=
  ∀ a ∈ xs, ∀ b ∈ xs, Ancestor T a b → a = b

theorem children_antichain (v : Fin n) : RootAntichain T (children T O v) :=
  fun _ ha _ hb h => children_incomparable T O ha hb h

theorem antichain_common_descendant {xs : List (Fin n)} (h : RootAntichain T xs)
    {a b u : Fin n} (ha : a ∈ xs) (hb : b ∈ xs)
    (hau : Ancestor T a u) (hbu : Ancestor T b u) : a = b := by
  rcases TreeAncestry.comparable hau hbu with k | k
  · exact h a ha b hb k
  · exact (h b hb a ha k).symm

theorem build_labels_nodup (fuel : Nat) (xs : List (Fin n))
    (hn : xs.Nodup) (ha : RootAntichain T xs)
    (hf : ∀ v ∈ xs, n-v.val ≤ fuel) : (labels (build T O fuel xs)).Nodup := by
  induction fuel generalizing xs with
  | zero => simp [build,labels]
  | succ fuel ih =>
    induction xs with
    | nil => simp [labels]
    | cons v vs ht =>
      obtain ⟨hv,hn'⟩ := List.nodup_cons.mp hn
      have hf' : ∀ w ∈ vs, n-w.val ≤ fuel+1 := fun w hw => hf w (by simp [hw])
      have ha' : RootAntichain T vs := fun a h₁ b h₂ h => ha a (by simp [h₁]) b (by simp [h₂]) h
      have hch : ∀ w ∈ children T O v, n-w.val ≤ fuel :=
        fun _ hw => child_fuel T O (hf v (by simp)) hw
      have hl := ih (children T O v) (children_nodup T O v) (children_antichain T O v) hch
      have hr := ht hn' ha' hf'
      have root_left : v ∉ labels (build T O fuel (children T O v)) := by
        intro hh
        obtain ⟨w,hw,hA⟩ := (mem_build_labels T O fuel _ hch v).mp hh
        have hg := child_gt T O hw
        have hb := hA.val_le
        omega
      have root_right : v ∉ labels (build T O (fuel+1) vs) := by
        intro hh
        obtain ⟨w,hw,hA⟩ := (mem_build_labels T O (fuel+1) _ hf' v).mp hh
        have he : w = v := ha w (by simp [hw]) v (by simp) hA
        exact hv (he ▸ hw)
      have disjoint : ∀ a ∈ labels (build T O fuel (children T O v)),
          ∀ b ∈ labels (build T O (fuel+1) vs), a ≠ b := by
        intro a hal b hbr he
        subst b
        obtain ⟨c,hc,hca⟩ := (mem_build_labels T O fuel _ hch a).mp hal
        obtain ⟨w,hw,hwa⟩ := (mem_build_labels T O (fuel+1) _ hf' a).mp hbr
        have hva := (child_ancestor T O hc).trans hca
        have hve : v = w := antichain_common_descendant T ha (by simp) (by simp [hw]) hva hwa
        exact hv (hve.symm ▸ hw)
      rw [build,labels]
      apply List.nodup_cons.mpr
      exact ⟨by simpa only [List.mem_append, not_or] using And.intro root_left root_right,
        List.nodup_append.mpr ⟨hl,hr,disjoint⟩⟩

theorem labels_length {α : Type} (t : BinaryTree α) : (labels t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [labels, hl, hr, BinaryTree.numNodes, Nat.add_assoc]

theorem root_shape_nodup (r : Fin n) : (labels (build T O n [r])).Nodup := by
  apply build_labels_nodup T O n [r] (by simp)
  · intro a ha b hb _
    have he : a = r := by simpa using ha
    have he' : b = r := by simpa using hb
    exact he.trans he'.symm
  · intro v _; exact Nat.sub_le _ _

/-- Exactly one positively weighted binary-tree node per original vertex. -/
theorem root_shape_numNodes (r : Fin n) (hr : r.val = 0) :
    (build T O n [r]).numNodes = n := by
  classical
  have he : (labels (build T O n [r])).toFinset = Finset.univ := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact root_shape_complete T O r hr u
  rw [← labels_length, ← List.toFinset_card_of_nodup (root_shape_nodup T O r), he]
  simp

#print axioms build_labels_nodup
#print axioms root_shape_numNodes
end StackSorting.FinitePort.ChildSibling
