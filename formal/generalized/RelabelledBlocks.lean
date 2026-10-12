import IntervalMinimum

/-! Exact relabelling transport for physical pop images and interval blocks. -/
namespace StackSorting.Generalized

variable {α β : Type}

/-- Injective relabelling loses no physical pop alternatives. -/
theorem Step.pop_map_iff {r s : Nat} {xs : List α} {x : α} {ys : List β}
    (f : α → β) (hf : Function.Injective f) :
    Step r s (xs.map f) [] [f x] ys ↔
      ∃ zs, Step r s xs [] [x] zs ∧ ys = zs.map f := by
  constructor
  · intro h
    generalize he : xs.map f = held at h
    cases h with
    | pop pre post y allowed =>
        obtain ⟨as, bs, hx, hpre, hpost⟩ := List.map_eq_append_iff.mp he
        obtain ⟨z, zs, hbs, hz, hzs⟩ := List.map_eq_cons_iff.mp hpost
        have hzx : z = x := hf hz
        subst z
        subst bs
        subst xs
        subst pre
        subst post
        refine ⟨as ++ zs, Step.pop as zs x (by simpa using allowed), ?_⟩
        simp
  · rintro ⟨zs, h, rfl⟩
    simpa using h.map f

/-- Pushes also lift through any relabelling; injectivity is unnecessary
because the newly read token is already specified. -/
theorem Step.push_map_iff {r s : Nat} {xs : List α} {x : α} {ys : List β}
    (f : α → β) :
    Step r s (xs.map f) [f x] [] ys ↔
      ∃ zs, Step r s xs [x] [] zs ∧ ys = zs.map f := by
  constructor
  · intro h
    generalize he : xs.map f = held at h
    cases h with
    | push pre post y allowed =>
        obtain ⟨as, bs, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp he
        exact ⟨as ++ x :: bs, Step.push as bs x (by simpa using allowed), by simp⟩
  · rintro ⟨zs, h, rfl⟩
    simpa using h.map f

/-- Exact lift of a push-only history through an arbitrary rank embedding. -/
theorem Run.lift_push_map {s : Nat} {held input output final : List β}
    (h : Run 2 s held input output final) (emptyOutput : output = [])
    (f : α → β) (xs ins : List α) (hheld : held = xs.map f)
    (hinput : input = ins.map f) :
    ∃ ys, Run 2 s xs ins [] ys ∧ final = ys.map f := by
  induction h generalizing xs ins with
  | nil held =>
      have hi : ins = [] := by simpa using hinput.symm
      subst ins
      exact ⟨xs, Run.nil xs, hheld⟩
  | @cons held middle final input output inputs outputs head rest ih =>
      cases head with
      | push pre post y allowed =>
          have he : ins.map f = y :: inputs := by simpa using hinput.symm
          obtain ⟨x, tail, rfl, rfl, hi⟩ := List.map_eq_cons_iff.mp he
          have hp : Step 2 s (xs.map f) [f x] [] (pre ++ f x :: post) := by
            simpa [← hheld] using (Step.push (r := 2) (s := s) pre post (f x) allowed)
          obtain ⟨middle, hm, hmid⟩ := (Step.push_map_iff f).mp hp
          have ht : outputs = [] := by simpa using emptyOutput
          obtain ⟨ys, hr, hf⟩ := ih ht middle tail hmid hi.symm
          exact ⟨ys, by simpa using Run.cons hm hr, hf⟩
      | pop pre post x allowed => simp at emptyOutput

/-- The physical orders represented by a block on arbitrary distinct labels. -/
def RankBlock (f : Nat → α) (base top : Nat) (xs : List α) : Prop :=
  ∃ ranks, SegmentOrder base top ranks ∧ xs = ranks.map f

theorem RankBlock.minimum_image (f : Nat → α) (hf : Function.Injective f)
    {base top cut s : Nat} {ys : List α}
    (hbc : base < cut) (hct : cut ≤ top) (hs : s = top-cut+1) :
    (∃ xs, RankBlock f base top xs ∧ Step 2 s xs [] [f base] ys) ↔
      ∃ high, RankBlock f cut top high ∧
        ys = high ++ ((List.range' (base+1) (cut-base-1)).reverse.map f) := by
  constructor
  · rintro ⟨xs, ⟨ranks, hr, rfl⟩, hp⟩
    obtain ⟨zs, hz, rfl⟩ := (Step.pop_map_iff f hf).mp hp
    obtain ⟨high, hh, rfl⟩ :=
      (SegmentOrder.minimum_image hbc hct hs).mp ⟨ranks, hr, hz⟩
    exact ⟨high.map f, ⟨high, hh, rfl⟩, by simp⟩
  · rintro ⟨high, ⟨ranks, hr, rfl⟩, rfl⟩
    obtain ⟨xs, hx, hp⟩ := (SegmentOrder.minimum_image hbc hct hs).mpr ⟨ranks, hr, rfl⟩
    exact ⟨xs.map f, ⟨xs, hx, rfl⟩, by simpa using hp.map f⟩

#print axioms Step.pop_map_iff
#print axioms RankBlock.minimum_image
end StackSorting.Generalized
