import SmallBlocks

namespace StackSorting.Generalized

/-- Read a specified batch without outputs, then output its specified record. -/
def RecordStep (s : Nat) (input : List Nat) (a : Nat) (held after : List Nat) : Prop :=
  ∃ before, Run 2 s held input [] before ∧ Step 2 s before [] [a] after

/-- The U and W cycles at once: a singleton highest block reads two new
labels, emits the second and then its old label, and remains a singleton.
Any frozen suffix is preserved exactly. -/
theorem singleton_record_cycle (f : Nat → Nat) (hf : Function.Injective f)
    (s : Nat) (tail final : List Nat) (hs : 2 ≤ s)
    (hold : f 0 ∉ tail) (hnew : f 2 ∉ tail) :
    (∃ middle, RecordStep s [f 1,f 2] (f 2) (f 0 :: tail) middle ∧
      Step 2 s middle [] [f 0] final) ↔ final = f 1 :: tail := by
  have himage (middle : List Nat) :
      RecordStep s [f 1,f 2] (f 2) (f 0 :: tail) middle ↔
      ∃ high, RankBlock f 0 2 high ∧ middle = high ++ tail := by
    have hz := RankBlock.record_image_suffix f hf (base := 0) (top := 1)
      (s := s) 1 tail middle (by omega) hs hnew
    simpa [rankBlock_one_iff, RecordStep, List.range'_succ] using hz
  have hne : f 0 ≠ f 1 := fun he => by have := hf he; omega
  constructor
  · rintro ⟨middle, hr, hp⟩
    obtain ⟨high, hh, rfl⟩ := (himage middle).mp hr
    obtain ⟨after, ha, rfl⟩ := hp.pop_suffix hold
    rcases (rankBlock_two_iff f high).mp hh with rfl | rfl
    · have he := ha.pop_result (by simp [hne])
      have hz : after = [f 1] := by simpa using he
      simp [hz]
    · have he := ha.pop_result (by simp [Ne.symm hne])
      have hz : after = [f 1] := by simpa [Ne.symm hne] using he
      simp [hz]
  · rintro rfl
    refine ⟨f 0 :: f 1 :: tail, ?_, ?_⟩
    · apply (himage _).mpr
      exact ⟨[f 0,f 1], (rankBlock_two_iff f _).mpr (Or.inl rfl), rfl⟩
    · simpa using Step.pop (r := 2) (s := s) [] (f 1 :: tail) (f 0) (by simp; omega)

/-- The repaired V cycle: either order of two held labels reads two new
labels and emits the new record followed by the old larger held label.
Exactly both orders of the remaining pair are possible. -/
theorem pair_record_cycle (f : Nat → Nat) (hf : Function.Injective f)
    (s : Nat) (final : List Nat) (hs : 3 ≤ s) :
    (∃ held middle, RankBlock f 0 2 held ∧
      RecordStep s [f 2,f 3] (f 3) held middle ∧
      Step 2 s middle [] [f 1] final) ↔
      final = [f 0,f 2] ∨ final = [f 2,f 0] := by
  have himage (middle : List Nat) :
      (∃ held, RankBlock f 0 2 held ∧ RecordStep s [f 2,f 3] (f 3) held middle) ↔
      RankBlock f 0 3 middle := by
    have hz := RankBlock.record_image_suffix f hf (base := 0) (top := 2)
      (s := s) 1 [] middle (by omega) (by omega) (by simp)
    simpa [RecordStep, List.range'_succ] using hz
  have h01 : f 0 ≠ f 1 := fun he => by have := hf he; omega
  have h02 : f 0 ≠ f 2 := fun he => by have := hf he; omega
  have h12 : f 1 ≠ f 2 := fun he => by have := hf he; omega
  have h21 : f 2 ≠ f 1 := Ne.symm h12
  have h10 : f 1 ≠ f 0 := Ne.symm h01
  have h20 : f 2 ≠ f 0 := Ne.symm h02
  constructor
  · rintro ⟨held, middle, hh, hr, hp⟩
    have hm := (himage middle).mp ⟨held, hh, hr⟩
    rcases (rankBlock_three_iff f middle).mp hm with rfl | rfl | rfl | rfl
    all_goals have he := hp.pop_result (by simp_all)
    all_goals simp_all
  · rintro (rfl | rfl)
    · have hm : RankBlock f 0 3 [f 0,f 2,f 1] :=
        (rankBlock_three_iff f _).mpr (Or.inl rfl)
      obtain ⟨held, hh, hr⟩ := (himage _).mpr hm
      exact ⟨held, _, hh, hr, by simpa using
        (Step.pop (r := 2) (s := s) [f 0,f 2] [] (f 1) (by simp; omega))⟩
    · have hm : RankBlock f 0 3 [f 2,f 1,f 0] :=
        (rankBlock_three_iff f _).mpr (Or.inr (Or.inr (Or.inr rfl)))
      obtain ⟨held, hh, hr⟩ := (himage _).mpr hm
      exact ⟨held, _, hh, hr, by simpa using
        (Step.pop (r := 2) (s := s) [f 2] [f 0] (f 1) (by simp; omega))⟩

#print axioms singleton_record_cycle
#print axioms pair_record_cycle
end StackSorting.Generalized
