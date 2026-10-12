import TwoPushBlocks

/-! The last pushed maximum is in one of the first two positions. Deleting it
has exactly the preceding block as its image, for every pop width at least two.
This certifies the local last-token operation used by every record batch. -/
namespace StackSorting.Generalized

/-- A push order is a permutation of exactly its introduced ranks. -/
theorem PushOrder.perm_range {n : Nat} {xs : List Nat} (h : PushOrder n xs) :
    xs.Perm (List.range n) := by
  induction h with
  | nil => rfl
  | @top n xs h ih =>
      simpa [List.range_succ] using (List.Perm.cons n ih).trans (by simpa using (List.perm_append_comm (l₁ := [n]) (l₂ := List.range n)))
  | @second n x xs h ih =>
      have ht : (x :: n :: xs).Perm (n :: x :: xs) := List.Perm.swap ..
      exact ht.trans (by simpa [List.range_succ] using
        (List.Perm.cons n ih).trans (by simpa using (List.perm_append_comm (l₁ := [n]) (l₂ := List.range n))))

theorem PushOrder.maximum_split {n : Nat} {xs : List Nat}
    (h : PushOrder (n+1) xs) :
    ∃ pre post, pre.length < 2 ∧ xs = pre ++ n :: post ∧
      PushOrder n (pre ++ post) := by
  cases h with
  | top h => exact ⟨[], _, by simp, rfl, h⟩
  | second h => exact ⟨[_], _, by simp, rfl, h⟩

theorem PushOrder.pop_maximum {n s : Nat} {xs : List Nat}
    (h : PushOrder (n+1) xs) (hs : 2 ≤ s) :
    ∃ ys, Step 2 s xs [] [n] ys ∧ PushOrder n ys := by
  obtain ⟨pre, post, hp, rfl, hrest⟩ := h.maximum_split
  exact ⟨pre ++ post, Step.pop pre post n (Nat.lt_of_lt_of_le hp hs), hrest⟩

/-- Every preceding order lifts to a top insertion and accessible maximum pop. -/
theorem PushOrder.lift_maximum {n s : Nat} {ys : List Nat}
    (h : PushOrder n ys) (hs : 0 < s) :
    ∃ xs, PushOrder (n+1) xs ∧ Step 2 s xs [] [n] ys := by
  refine ⟨n :: ys, h.top, ?_⟩
  simpa using Step.pop (r := 2) [] ys n hs

/-- On a duplicate-free stack the result of popping a given token is unique. -/
theorem Step.pop_result {r s x : Nat} {xs ys : List Nat}
    (h : Step r s xs [] [x] ys) (hd : xs.Nodup) : ys = xs.erase x := by
  cases h with
  | pop pre post x allowed =>
      have hn : x ∉ pre := by
        intro hx
        exact (List.nodup_append.mp hd).2.2 x hx x (by simp) rfl
      simp [List.erase_append_right _ hn]

theorem PushOrder.maximum_image {n s : Nat} {ys : List Nat} (hs : 2 ≤ s) :
    (∃ xs, PushOrder (n+1) xs ∧ Step 2 s xs [] [n] ys) ↔ PushOrder n ys := by
  constructor
  · rintro ⟨xs, horder, hpop⟩
    obtain ⟨zs, hpop', horder'⟩ := horder.pop_maximum hs
    have hd : xs.Nodup := horder.perm_range.nodup_iff.mpr List.nodup_range
    have he : ys = zs := (hpop.pop_result hd).trans (hpop'.pop_result hd).symm
    simpa [he] using horder'
  · intro h
    exact h.lift_maximum (by omega)

#print axioms PushOrder.perm_range
#print axioms PushOrder.maximum_split
#print axioms PushOrder.pop_maximum
#print axioms PushOrder.lift_maximum
#print axioms PushOrder.maximum_image
end StackSorting.Generalized
