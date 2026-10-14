import LocalIdempotentNode

namespace StackSorting.Simon
open FactorizationTree

variable {B M : Type*} [Monoid M] [Fintype M]

private theorem le_height_fold (xs : List ℕ) {x : ℕ} (hx : x ∈ xs) :
    x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

/-- An actual local-divisor tree can be transformed into an ambient tree.
Each local-tree level costs at most 3|M|+3 ambient levels. -/
theorem localForest_lift_valid (c : M) (interior : B → M)
    (t : FactorizationTree B) (hv : Valid (localBlockValue c interior) t) :
    HasTree (ambientBlockValue c interior) t.leaves
      ((3 * Fintype.card M + 3) * t.height) := by
  induction hv with
  | leaf b => simpa only [leaves, height, Nat.mul_zero] using
      hasTree_singleton (ambientBlockValue c interior) b 0
  | node ts hc ha hb ih =>
    let K := (ts.map height).foldr max 0
    let C := 3 * Fintype.card M + 3
    have hchild : ∀ r ∈ ts, HasTree (ambientBlockValue c interior) r.leaves (C * K) := by
      intro r hr
      apply hasTree_mono (ih r hr)
      exact Nat.mul_le_mul_left C (le_height_fold (ts.map height) (List.mem_map.mpr ⟨r,hr,rfl⟩))
    let ws := ts.map leaves
    have hws : ∀ w ∈ ws, HasTree (ambientBlockValue c interior) w (C * K) := by
      intro w hw
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hw
      exact hchild r hr
    have hjoined : HasTree (ambientBlockValue c interior) ws.flatten (C * K + C) := by
      rcases hb with hbinary | ⟨e,he,hvalues⟩
      · obtain ⟨r,s,hts⟩ := List.length_eq_two.mp hbinary
        subst ts
        have hpair := hasTree_binary (hchild r (by simp)) (hchild s (by simp))
        have hbound : C * K + 1 ≤ C * K + C := by dsimp [C]; omega
        simpa [ws] using hasTree_mono hpair hbound
      · have hnone : ∀ w ∈ ws, w ≠ [] := by
          intro w hw
          obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hw
          exact (hc r hr).leaves_ne_nil
        have hval : ∀ w ∈ ws, (w.map (localBlockValue c interior)).prod = e := by
          intro w hw
          obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hw
          exact hvalues r hr
        simpa [C, Nat.add_assoc] using hasTree_of_common_local_idempotent c interior ws
          (C * K) (by simpa [ws] using ha) hnone hws e he hval
    have hword : ws.flatten = (node ts).leaves := by simp [ws, leaves, List.flatMap_def]
    rw [← hword]
    apply hasTree_mono hjoined
    rw [height]
    change C * K + C ≤ C * (K + 1)
    simp only [Nat.mul_add, Nat.mul_one, le_refl]

theorem localForest_lift (c : M) (interior : B → M)
    (w : List B) (h : ℕ) (ht : HasTree (localBlockValue c interior) w h) :
    HasTree (ambientBlockValue c interior) w ((3 * Fintype.card M + 3) * h) := by
  obtain ⟨t,hw,hv,hh⟩ := ht
  have hl := localForest_lift_valid c interior t hv
  rw [hw] at hl
  exact hasTree_mono hl (Nat.mul_le_mul_left _ hh)

#print axioms localForest_lift
end StackSorting.Simon
