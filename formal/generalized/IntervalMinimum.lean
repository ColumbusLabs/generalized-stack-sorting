import MaximumBlockDeletion

/-! A shifted interval-partition language for local deletion proofs. -/
namespace StackSorting.Generalized

/-- Interval-partition orders of the half-open rank interval [base, top). -/
inductive SegmentOrder (base : Nat) : Nat → List Nat → Prop where
  | nil : SegmentOrder base base []
  | block (lo t : Nat) (xs : List Nat) (lower : SegmentOrder base lo xs) :
      SegmentOrder base (lo+t+1) ((lo :: (List.range' (lo+1) t).reverse) ++ xs)

theorem SegmentOrder.bounds {base top : Nat} {xs : List Nat}
    (h : SegmentOrder base top xs) : base ≤ top := by
  induction h with
  | nil => omega
  | block lo t xs lower ih => omega

theorem segmentOrder_zero (top : Nat) (xs : List Nat) :
    SegmentOrder 0 top xs ↔ IntervalOrder top xs := by
  constructor
  · intro h; induction h with
    | nil => exact .nil
    | block lo t xs lower ih => exact .block lo t xs ih
  · intro h; induction h with
    | nil => exact .nil
    | block lo t xs lower ih => exact .block lo t xs ih

/-- Adjacent rank segments concatenate from high to low. -/
theorem SegmentOrder.append {base middle top : Nat} {xs ys : List Nat}
    (high : SegmentOrder middle top xs) (low : SegmentOrder base middle ys) :
    SegmentOrder base top (xs ++ ys) := by
  induction high with
  | nil => simpa using low
  | block lo t xs lower ih =>
      simpa [List.append_assoc] using (SegmentOrder.block lo t (xs ++ ys) ih)

/-- The increasing list of inputs has precisely this length. -/
theorem SegmentOrder.length {base top : Nat} {xs : List Nat}
    (h : SegmentOrder base top xs) : xs.length + base = top := by
  induction h with
  | nil => simp
  | block lo t xs lower ih => simp; omega

/-- Every rank inside the segment occurs once. -/
theorem SegmentOrder.perm_range {base top : Nat} {xs : List Nat}
    (h : SegmentOrder base top xs) : xs.Perm (List.range' base (top-base)) := by
  induction h with
  | nil => simp
  | block lo t xs lower ih =>
      have hb := lower.bounds
      have hc : ((lo :: (List.range' (lo+1) t).reverse) ++ xs).Perm
          ((lo :: List.range' (lo+1) t) ++ List.range' base (lo-base)) :=
        (List.Perm.cons lo (List.reverse_perm _)).append ih
      have hr : lo :: List.range' (lo+1) t = List.range' lo (t+1) := by
        simp [List.range'_succ]
      rw [hr] at hc
      have hz := hc.trans (List.perm_append_comm)
      have he : List.range' base (lo-base) ++ List.range' lo (t+1) =
          List.range' base (lo+t+1-base) := by
        have hbase : base + (lo-base) = lo := by omega
        have hlen : lo-base+(t+1) = lo+t+1-base := by omega
        have hh := List.range'_append (s := base) (m := lo-base) (n := t+1) (step := 1)
        simpa [hbase, hlen] using hh
      exact he ▸ hz

/-- Locate the lowest interval, the unique interval containing the minimum. -/
theorem SegmentOrder.minimum_split {base top : Nat} {xs : List Nat}
    (h : SegmentOrder base top xs) (hne : base < top) :
    ∃ u high, base < u ∧ u ≤ top ∧ SegmentOrder u top high ∧
      xs = high ++ base :: (List.range' (base+1) (u-base-1)).reverse := by
  induction h with
  | nil => omega
  | block lo t xs lower ih =>
      have hb := lower.bounds
      by_cases he : lo = base
      · subst lo
        have hx : xs = [] := by
          have hl := lower.length
          have hz : xs.length = 0 := by omega
          exact List.length_eq_zero_iff.mp hz
        subst xs
        refine ⟨base+t+1, [], by omega, by omega, .nil, ?_⟩
        have ht : base+t+1-base-1 = t := by omega
        simp [ht]
      · obtain ⟨u, high, hu, hut, hh, hx⟩ := ih (by omega)
        refine ⟨u, (lo :: (List.range' (lo+1) t).reverse) ++ high,
          hu, by omega, SegmentOrder.block lo t high hh, ?_⟩
        simp [hx, List.append_assoc]

/-- Descending order is the partition into singleton intervals. -/
theorem SegmentOrder.descending (base len : Nat) :
    SegmentOrder base (base+len) (List.range' base len).reverse := by
  induction len with
  | zero => simpa using (SegmentOrder.nil (base := base))
  | succ len ih =>
      have hh := SegmentOrder.block (base+len) 0 _ ih
      simpa [List.range'_concat, List.reverse_append, Nat.add_assoc] using hh

/-- An accessible occurrence in a duplicate-free stack has its claimed index. -/
theorem Step.pop_index {r s x : Nat} {xs ys : List Nat}
    (h : Step r s xs [] [x] ys) (hd : xs.Nodup) : xs.idxOf x < s := by
  cases h with
  | pop pre post x allowed =>
      have hn : x ∉ pre := by
        intro hx
        exact (List.nodup_append.mp hd).2.2 x hx x (by simp) rfl
      simpa [List.idxOf_append, hn] using allowed

/-- The complete restricted minimum-pop image before collapsing its union. -/
theorem SegmentOrder.minimum_image_union {base top s : Nat} {ys : List Nat}
    (hne : base < top) :
    (∃ xs, SegmentOrder base top xs ∧ Step 2 s xs [] [base] ys) ↔
      ∃ u high, base < u ∧ u ≤ top ∧ SegmentOrder u top high ∧
        high.length < s ∧
        ys = high ++ (List.range' (base+1) (u-base-1)).reverse := by
  constructor
  · rintro ⟨xs, h, hp⟩
    obtain ⟨u, high, hu, hut, hh, hx⟩ := h.minimum_split hne
    have hn : base ∉ high := by
      intro hm
      have hz := hh.perm_range.mem_iff.mp hm
      obtain ⟨i, hi, he⟩ := List.mem_range'.mp hz
      omega
    have hd : xs.Nodup := h.perm_range.nodup_iff.mpr List.nodup_range'
    have hindex := hp.pop_index hd
    have hout := hp.pop_result hd
    refine ⟨u, high, hu, hut, hh, ?_, ?_⟩
    · simpa [hx, List.idxOf_append, hn] using hindex
    · simpa [hx, List.erase_append_right _ hn] using hout
  · rintro ⟨u, high, hu, hut, hh, hlen, rfl⟩
    have ht : base + (u-base-1) + 1 = u := by omega
    have low : SegmentOrder base u
        (base :: (List.range' (base+1) (u-base-1)).reverse) := by
      have hz := SegmentOrder.block base (u-base-1) [] (SegmentOrder.nil (base := base))
      simpa [ht] using hz
    refine ⟨high ++ base :: (List.range' (base+1) (u-base-1)).reverse,
      hh.append low, ?_⟩
    exact Step.pop high _ base hlen

/-- Exact restricted minimum-pop formula. `cut = top-s+1`; the top
` s-1 ` ranks remain one unrestricted block and all lower ranks are forced
into descending order. No union of extra states is left over. -/
theorem SegmentOrder.minimum_image {base top cut s : Nat} {ys : List Nat}
    (hbc : base < cut) (hct : cut ≤ top) (hs : s = top-cut+1) :
    (∃ xs, SegmentOrder base top xs ∧ Step 2 s xs [] [base] ys) ↔
      ∃ high, SegmentOrder cut top high ∧
        ys = high ++ (List.range' (base+1) (cut-base-1)).reverse := by
  rw [SegmentOrder.minimum_image_union (by omega : base < top)]
  constructor
  · rintro ⟨u, high, hu, hut, hh, hlen, rfl⟩
    have hsize := hh.length
    have hcu : cut ≤ u := by omega
    have hd : SegmentOrder cut u (List.range' cut (u-cut)).reverse := by
      have hz := SegmentOrder.descending cut (u-cut)
      have he : cut+(u-cut) = u := by omega
      simpa [he] using hz
    refine ⟨high ++ (List.range' cut (u-cut)).reverse, hh.append hd, ?_⟩
    have hstart : base+1+(cut-base-1) = cut := by omega
    have hsum : cut-base-1+(u-cut) = u-base-1 := by omega
    have hr : List.range' (base+1) (cut-base-1) ++ List.range' cut (u-cut) =
        List.range' (base+1) (u-base-1) := by
      have hz := List.range'_append (s := base+1) (m := cut-base-1)
        (n := u-cut) (step := 1)
      simpa [hstart, hsum] using hz
    rw [← hr, List.reverse_append, List.append_assoc]
  · rintro ⟨high, hh, rfl⟩
    have hsize := hh.length
    exact ⟨cut, high, hbc, hct, hh, by omega, rfl⟩

/-- In the case used by the intact infinite-family prefix, popping the minimum
from a block one larger than the pop width forces precisely one bottom token. -/
theorem SegmentOrder.minimum_image_one_blocker {base s : Nat} {ys : List Nat}
    (hs : 1 ≤ s) :
    (∃ xs, SegmentOrder base (base+s+1) xs ∧ Step 2 s xs [] [base] ys) ↔
      ∃ high, SegmentOrder (base+2) (base+s+1) high ∧ ys = high ++ [base+1] := by
  have hz := SegmentOrder.minimum_image (ys := ys) (base := base)
    (top := base+s+1) (cut := base+2) (s := s) (by omega) (by omega) (by omega)
  have he : base+2-base-1 = 1 := by omega
  simpa [he] using hz

#print axioms segmentOrder_zero
#print axioms SegmentOrder.append
#print axioms SegmentOrder.perm_range
#print axioms SegmentOrder.minimum_split
#print axioms SegmentOrder.minimum_image_union
#print axioms SegmentOrder.minimum_image
#print axioms SegmentOrder.minimum_image_one_blocker
end StackSorting.Generalized
