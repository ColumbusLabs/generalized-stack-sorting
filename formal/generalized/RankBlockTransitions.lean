import BlockPushClosure

/-! Relabelled block transitions above an arbitrary frozen lower suffix. -/
namespace StackSorting.Generalized

variable {α : Type}

theorem RankBlock.read_image_suffix (f : Nat → α) {base top s : Nat} (k : Nat)
    (tail final : List α) (hb : base < top) :
    (∃ held, RankBlock f base top held ∧
      Run 2 s (held ++ tail) ((List.range' top k).map f) [] final) ↔
      ∃ high, RankBlock f base (top+k) high ∧ final = high ++ tail := by
  constructor
  · rintro ⟨held, ⟨ranks, hh, rfl⟩, hr⟩
    have hne : ranks.map f ≠ [] := by
      have hlen := hh.length
      intro he
      have hz : ranks = [] := by simpa using he
      simp [hz] at hlen
      omega
    obtain ⟨high, hs, rfl⟩ := hr.strip_push_suffix rfl (ranks.map f) tail rfl hne
    obtain ⟨zs, hz, rfl⟩ := hs.lift_push_map rfl f ranks (List.range' top k) rfl rfl
    exact ⟨zs.map f, ⟨zs, hz.continueSegment rfl hh rfl, rfl⟩, rfl⟩
  · rintro ⟨high, ⟨ranks, hh, rfl⟩, rfl⟩
    obtain ⟨held, hs, hr⟩ := (SegmentOrder.read_image k ranks (Nat.le_of_lt hb)).mpr hh
    exact ⟨held.map f, ⟨held, hs, rfl⟩, by simpa using (hr.map f).append_suffix tail⟩

theorem Step.pop_mem {r s : Nat} {held final : List α} {x : α}
    (h : Step r s held [] [x] final) : x ∈ held := by
  cases h with
  | pop pre post x allowed => simp

/-- Popping a value absent from a frozen suffix acts entirely in the prefix. -/
theorem Step.pop_suffix {r s : Nat} {xs tail final : List α} {x : α}
    (h : Step r s (xs ++ tail) [] [x] final) (hne : x ∉ tail) :
    ∃ ys, Step r s xs [] [x] ys ∧ final = ys ++ tail := by
  induction xs generalizing s final with
  | nil => exact (hne (by simpa using h.pop_mem)).elim
  | cons a xs ih =>
      generalize he : (a :: xs) ++ tail = held at h
      cases h with
      | pop pre post x allowed =>
          cases pre with
          | nil =>
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
              rcases he with ⟨rfl, rfl⟩
              exact ⟨xs, by simpa using (Step.pop (r := r) [] xs a allowed), rfl⟩
          | cons b pre =>
              simp only [List.cons_append, List.cons.injEq] at he
              rcases he with ⟨rfl, he⟩
              have hp : Step r (s-1) (xs ++ tail) [] [x] (pre ++ post) := by
                rw [he]
                exact Step.pop pre post x (by simp at allowed; omega)
              obtain ⟨ys, hs, hout⟩ := ih hp
              have hfull : Step r s (a :: xs) [] [x] (a :: ys) := by
                cases hs with
                | pop p q x bound =>
                    simpa using (Step.pop (r := r) (s := s) (a :: p) q x (by simp; omega))
              exact ⟨a :: ys, hfull, by simpa using congrArg (List.cons a) hout⟩

theorem SegmentOrder.maximum_image {base top s : Nat} {ys : List Nat}
    (hb : base ≤ top) (hs : 2 ≤ s) :
    (∃ xs, SegmentOrder base (top+1) xs ∧ Step 2 s xs [] [top] ys) ↔
      SegmentOrder base top ys := by
  constructor
  · rintro ⟨xs, hx, hp⟩
    obtain ⟨zs, hz, hpush⟩ := hx.unpush hb s
    have hpop : Step 2 s xs [] [top] zs := by
      cases hpush with
      | push pre post top allowed => exact Step.pop pre post top (by omega)
    have hd : xs.Nodup := hx.perm_range.nodup_iff.mpr List.nodup_range'
    have he : ys = zs := (hp.pop_result hd).trans (hpop.pop_result hd).symm
    simpa [he] using hz
  · intro hy
    exact ⟨top :: ys, hy.push_top, by simpa using
      (Step.pop (r := 2) (s := s) [] ys top (by simp; omega))⟩

theorem RankBlock.maximum_image (f : Nat → α) (hf : Function.Injective f)
    {base top s : Nat} {ys : List α} (hb : base ≤ top) (hs : 2 ≤ s) :
    (∃ xs, RankBlock f base (top+1) xs ∧ Step 2 s xs [] [f top] ys) ↔
      RankBlock f base top ys := by
  constructor
  · rintro ⟨xs, ⟨ranks, hr, rfl⟩, hp⟩
    obtain ⟨zs, hz, rfl⟩ := (Step.pop_map_iff f hf).mp hp
    exact ⟨zs, (SegmentOrder.maximum_image hb hs).mp ⟨ranks, hr, hz⟩, rfl⟩
  · rintro ⟨ranks, hr, rfl⟩
    obtain ⟨xs, hx, hp⟩ := (SegmentOrder.maximum_image hb hs).mpr hr
    exact ⟨xs.map f, ⟨xs, hx, rfl⟩, by simpa using hp.map f⟩

/-- Exact arbitrary-label record-batch image above a frozen lower suffix.
The initial block is nonempty; `k+1` inputs are read and the final one is popped.
The `k` earlier new labels enlarge the top block, with no hidden alternatives. -/
theorem RankBlock.record_image_suffix (f : Nat → α) (hf : Function.Injective f)
    {base top s : Nat} (k : Nat) (tail final : List α)
    (hb : base < top) (hs : 2 ≤ s) (fresh : f (top+k) ∉ tail) :
    (∃ held before, RankBlock f base top held ∧
      Run 2 s (held ++ tail) ((List.range' top (k+1)).map f) [] before ∧
      Step 2 s before [] [f (top+k)] final) ↔
      ∃ high, RankBlock f base (top+k) high ∧ final = high ++ tail := by
  constructor
  · rintro ⟨held, before, hh, hr, hp⟩
    obtain ⟨high, hhigh, rfl⟩ :=
      (RankBlock.read_image_suffix f (k+1) tail before hb).mp ⟨held, hh, hr⟩
    obtain ⟨after, ha, rfl⟩ := hp.pop_suffix fresh
    have hlarge : RankBlock f base (top+k+1) high := by
      simpa [Nat.add_assoc] using hhigh
    exact ⟨after, (RankBlock.maximum_image f hf (by omega) hs).mp
      ⟨high, hlarge, ha⟩, rfl⟩
  · rintro ⟨high, hh, rfl⟩
    obtain ⟨before, hb', hp⟩ := (RankBlock.maximum_image f hf (by omega) hs).mpr hh
    have hlarge : RankBlock f base (top+(k+1)) before := by
      simpa [Nat.add_assoc] using hb'
    obtain ⟨held, hheld, hr⟩ :=
      (RankBlock.read_image_suffix f (k+1) tail (before ++ tail) hb).mpr
        ⟨before, hlarge, rfl⟩
    exact ⟨held, before ++ tail, hheld, hr, hp.append_suffix tail⟩

#print axioms RankBlock.read_image_suffix
#print axioms Step.pop_suffix
#print axioms SegmentOrder.maximum_image
#print axioms RankBlock.maximum_image
#print axioms RankBlock.record_image_suffix
end StackSorting.Generalized
