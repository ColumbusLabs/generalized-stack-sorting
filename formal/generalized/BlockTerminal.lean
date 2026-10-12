import BlockCycles

namespace StackSorting.Generalized

theorem Step.pop_index_bound {r s x : Nat} {xs ys : List Nat}
    (h : Step r s xs [] [x] ys) : xs.idxOf x < s := by
  cases h with
  | pop pre post x allowed =>
      by_cases hm : x ∈ pre
      · have hi := List.idxOf_lt_length_of_mem hm
        simpa [List.idxOf_append, hm] using (Nat.lt_trans hi allowed)
      · simpa [List.idxOf_append, hm] using allowed

/-- At least s tokens permanently above the requested value make this pop
impossible, independently of any lower suffix. -/
theorem no_pop_below {r s x : Nat} (high tail final : List Nat)
    (height : s ≤ high.length) (absent : x ∉ high) :
    ¬ Step r s (high ++ x :: tail) [] [x] final := by
  intro h
  have hi := h.pop_index_bound
  simp [List.idxOf_append, absent] at hi
  omega

/-- The intact U terminal is blocked in every physical history of its
normalized record segment: the permanent token lies below exactly s others. -/
theorem singleton_terminal_obstruction (f : Nat → Nat) (hf : Function.Injective f)
    (s p : Nat) (hs : 2 ≤ s) (absent : ∀ k, f k ≠ p) (final : List Nat) :
    ¬ ∃ middle, RecordStep s ((List.range' 1 s).map f) (f s) [f 0,p] middle ∧
      Step 2 s middle [] [p] final := by
  rintro ⟨middle, hr, hp⟩
  have hcount : s-1+1 = s := by omega
  have hlast : 1+(s-1) = s := by omega
  have himage := RankBlock.record_image_suffix f hf (base := 0) (top := 1)
    (s := s) (s-1) [p] middle (by omega) hs (by simpa [hlast] using absent s)
  have hhimage : (∃ before, Run 2 s [f 0,p] ((List.range' 1 s).map f) [] before ∧
        Step 2 s before [] [f s] middle) ↔
      ∃ high, RankBlock f 0 s high ∧ middle = high ++ [p] := by
    simpa [rankBlock_one_iff, hcount, hlast] using himage
  obtain ⟨high, ⟨ranks, hrank, rfl⟩, rfl⟩ := hhimage.mp hr
  have hlen : (ranks.map f).length = s := by
    have hz := hrank.length
    simpa using hz
  have hn : p ∉ ranks.map f := by
    intro hm
    obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
    exact absent k he
  exact no_pop_below (ranks.map f) [] final (by omega) hn hp

/-- Any reversed word of length at most s can be drained in forward order. -/
theorem Run.drain_reverse (s : Nat) (xs : List Nat) (hsize : xs.length ≤ s) :
    Run 2 s xs.reverse [] xs [] := by
  induction xs with
  | nil => exact Run.nil []
  | cons x xs ih =>
      have hs : xs.length < s := by simp at hsize; omega
      have hp : Step 2 s (xs.reverse ++ [x]) [] [x] xs.reverse := by
        simpa using Step.pop (r := 2) (s := s) xs.reverse [] x (by simpa using hs)
      simpa using Run.cons hp (ih (by omega))

/-- The repaired terminal block, one larger than the pop width, has a complete
increasing drain. The proof uses the exact restricted minimum-pop image and
then physically pops the exposed second-smallest label and drains the rest. -/
theorem RankBlock.terminal_repair (f : Nat → Nat) (hf : Function.Injective f)
    (s : Nat) (hs : 2 ≤ s) :
    ∃ held, RankBlock f 0 (s+1) held ∧
      Run 2 s held [] ((List.range (s+1)).map f) [] := by
  let high := ((List.range' 2 (s-1)).reverse).map f
  have hrank : SegmentOrder 2 (s+1) (List.range' 2 (s-1)).reverse := by
    have hz := SegmentOrder.descending 2 (s-1)
    have he : 2+(s-1) = s+1 := by omega
    simpa [he] using hz
  have hh : RankBlock f 2 (s+1) high := ⟨_, hrank, rfl⟩
  have hmin := RankBlock.minimum_image f hf (base := 0) (top := s+1)
    (cut := 2) (s := s) (ys := high ++ [f 1]) (by omega) (by omega) (by omega)
  obtain ⟨held, hheld, hpop⟩ := hmin.mpr ⟨high, hh, by simp⟩
  have hlen : high.length = s-1 := by simp [high]
  have hp : Step 2 s (high ++ [f 1]) [] [f 1] high := by
    simpa using Step.pop (r := 2) (s := s) high [] (f 1) (by rw [hlen]; omega)
  have hd : Run 2 s high [] ((List.range' 2 (s-1)).map f) [] := by
    have hz := Run.drain_reverse s ((List.range' 2 (s-1)).map f) (by simp)
    simpa [high] using hz
  have hout : (List.range (s+1)).map f = f 0 :: f 1 :: (List.range' 2 (s-1)).map f := by
    have he : s+1 = (s-1)+1+1 := by omega
    rw [List.range_eq_range', he]
    simp [List.range'_succ]
  exact ⟨held, hheld, by simpa [hout] using Run.cons hpop (Run.cons hp hd)⟩

/-- Repaired V terminal: read s fresh labels, output their last label, then
permanent, relay and remaining blockers in increasing order. -/
theorem pair_terminal_repair (f : Nat → Nat) (hf : Function.Injective f)
    (s : Nat) (hs : 3 ≤ s) :
    ∃ held, RankBlock f 0 2 held ∧
      Run 2 s held ((List.range' 2 s).map f)
        (f (s+1) :: (List.range (s+1)).map f) [] := by
  obtain ⟨after, ha, hr⟩ := RankBlock.terminal_repair f hf s (by omega)
  have hb : RankBlock f 0 (2+(s-1)) after := by
    have he : 2+(s-1) = s+1 := by omega
    simpa [he] using ha
  obtain ⟨held, before, hh, hread, hpop⟩ :=
    (RankBlock.record_image_suffix f hf (base := 0) (top := 2) (s := s)
      (s-1) [] after (by omega) (by omega) (by simp)).mpr ⟨after, hb, by simp⟩
  have hcount : s-1+1 = s := by omega
  have hlast : 2+(s-1) = s+1 := by omega
  exact ⟨held, hh, by simpa [hcount, hlast] using hread.append (Run.cons hpop hr)⟩

/-- Alternate W terminal after a deleted record. -/
theorem singleton_terminal_repair (f : Nat → Nat) (hf : Function.Injective f)
    (s : Nat) (hs : 3 ≤ s) :
    Run 2 s [f 0] ((List.range' 1 (s+1)).map f)
      (f (s+1) :: (List.range (s+1)).map f) [] := by
  obtain ⟨after, ha, hr⟩ := RankBlock.terminal_repair f hf s (by omega)
  have hb : RankBlock f 0 (1+s) after := by simpa [Nat.add_comm] using ha
  obtain ⟨held, before, hh, hread, hpop⟩ :=
    (RankBlock.record_image_suffix f hf (base := 0) (top := 1) (s := s)
      s [] after (by omega) (by omega) (by simp)).mpr ⟨after, hb, by simp⟩
  have he := (rankBlock_one_iff f held).mp hh
  simpa [he, Nat.add_comm] using hread.append (Run.cons hpop hr)

#print axioms no_pop_below
#print axioms singleton_terminal_obstruction
#print axioms RankBlock.terminal_repair
#print axioms pair_terminal_repair
#print axioms singleton_terminal_repair
end StackSorting.Generalized
