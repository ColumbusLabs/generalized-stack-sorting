import EqualFamily

/-! Universal rejection of the equal-width families (Section 4 of
`docs/infinite-basis-equal-width-draft.md`).

For every `r >= 3` and `k`, no unrestricted history of the slot-indexed
`(r,r)` machine generates `famA r k` or `famB r k` from increasing input.
Arbitrary histories are first made lazy (`generated_rangeLazy`, proved for
arbitrary widths). The proof then follows the literal bottom token: the low
phase pins `P = r-1` at depth `r-1` (Lemma 4.1); the record `M1` must put
`C = 3r-2` below `P`, since otherwise `P` is buried at depth `r`; every step
keeps `C` at the bottom at depth `r-2`, since otherwise `a_j` is buried at
depth `r` (Lemma 4.2); and the final records bury `C` at depth `r` or more
(Lemma 4.3). Capacity is unbounded throughout. -/
namespace StackSorting.Generalized
namespace Equal
open Unequal (Shape split_above_bottom pop_above_bottom read_above_bottom initial_read
  lowSeg lowSeg_append)

theorem Run.empty_eq {r s : Nat} {held input output final : List Nat}
    (h : Run r s held input output final) (hi : input = []) (ho : output = []) :
    final = held := by
  cases h with
  | nil => rfl
  | cons head tail =>
    cases head with
    | push => simp at hi
    | pop => simp at ho

/-- A history that reads exactly one token and outputs nothing is one push. -/
theorem Run.single_push {r s : Nat} {held input output after : List Nat} {x : Nat}
    (h : Run r s held input output after) (hi : input = [x]) (ho : output = []) :
    Step r s held [x] [] after := by
  cases h with
  | nil => simp at hi
  | cons head tail =>
    cases head with
    | pop => simp at ho
    | push pre post y allowed =>
      have hy : y = x ∧ _ := List.cons_eq_cons.mp (by simpa using hi)
      obtain ⟨rfl, hrest⟩ := hy
      rw [Run.empty_eq tail (by simpa using hrest) (by simpa using ho)]
      exact Step.push pre post y allowed

/-- A push into a stack with bottom token `z` either lands above `z` or goes
to the very bottom, below `z`. -/
theorem push_cases {r s : Nat} {ys after : List Nat} {x z : Nat}
    (h : Step r s (ys ++ [z]) [x] [] after) (hx : x ≠ z) (hz : z ∉ ys) :
    (∃ ys', after = ys' ++ [z] ∧ ys'.length = ys.length + 1 ∧ z ∉ ys') ∨
      after = (ys ++ [z]) ++ [x] := by
  generalize hh : ys ++ [z] = held at h
  generalize hi : [x] = input at h
  cases h with
  | push pre post y allowed =>
    have hy : x = y := by simpa using hi
    subst hy
    by_cases hl : pre.length ≤ ys.length
    · obtain ⟨t, hys, hpost⟩ := split_above_bottom hh.symm hl
      left
      refine ⟨pre ++ x :: t, by simp [hpost], by simp [hys]; omega, ?_⟩
      intro hm
      simp only [List.mem_append, List.mem_cons] at hm
      rcases hm with hm | hm | hm
      · exact hz (by simp [hys, hm])
      · exact hx hm.symm
      · exact hz (by simp [hys, hm])
    · right
      have hlen := congrArg List.length hh
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      have hpost : post = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hpost
      simp only [List.append_nil] at hh
      rw [← hh]
      simp

/-- A record reading at least one token above a bottom token `z` at depth
`r-2`. The first token read either lands above `z`, or goes below it and
becomes the new bottom; in both cases every later token lands above the
bottom, which ends at depth `r-2+(a-next)`. -/
theorem record_split {r limit z d next a : Nat} {st out : List Nat}
    (hs : Shape z d next st) (hd : d + 2 = r) (ha : next < a)
    (h : RangeLazyRun r r limit next st (a :: out)) :
    ∃ w st', (w = z ∨ w = next) ∧ Shape w (d + (a - next)) (a+1) st' ∧
      RangeLazyRun r r limit (a+1) st' out := by
  have hzn := hs.bottom_lt
  obtain ⟨ys, rfl, hl, hz, hb⟩ := hs
  rcases h.cons_cases with ⟨after, pop, tail⟩ |
    ⟨before, after, lower, upper, fresh, read, pop, tail⟩
  · have hm := hb a (Step.pop_mem' pop)
    omega
  · have hsplit : List.range' next (a+1-next) = [next] ++ List.range' (next+1) (a-next) := by
      have he : a+1-next = (a-next)+1 := by omega
      rw [he, List.range'_succ]
      rfl
    obtain ⟨mid, h₁, h₂⟩ := read.noOutputSplit rfl _ _ hsplit
    have hpush := Run.single_push h₁ rfl rfl
    have hbound : ∀ x ∈ after, x < a+1 := by
      intro x hx
      rcases pop.mem_after hx with hx | hx
      · rcases read.mem_after hx with hx | hx
        · have := hb x hx; omega
        · rw [List.mem_range'] at hx; omega
      · simp at hx
    have hfin : ∀ (w : Nat) (ys₁ : List Nat), mid = ys₁ ++ [w] → ys₁.length = d + 1 →
        w ∉ ys₁ → w < next + 1 →
        ∃ st', Shape w (d + (a - next)) (a+1) st' ∧ RangeLazyRun r r limit (a+1) st' out := by
      intro w ys₁ hm hl₁ hw₁ hwn
      have hwr : w ∉ List.range' (next+1) (a-next) := by
        intro hm'; rw [List.mem_range'] at hm'; omega
      obtain ⟨ys₂, hb₂, hl₂, hw₂⟩ := read_above_bottom h₂ rfl ys₁ w hm (by omega) hw₁ hwr
      rw [hb₂] at pop
      obtain ⟨ys₃, ha₃, hl₃, hw₃⟩ := pop_above_bottom pop (by omega) hw₂
      refine ⟨after, ⟨ys₃, ha₃, ?_, hw₃, hbound⟩, tail⟩
      simp only [List.length_range'] at hl₂
      omega
    rcases push_cases hpush (by omega) hz with ⟨ys₁, hm, hl₁, hz₁⟩ | hm
    · obtain ⟨st', hs', ht'⟩ := hfin z ys₁ hm (by omega) hz₁ (by omega)
      exact ⟨z, st', Or.inl rfl, hs', ht'⟩
    · have hn : next ∉ ys ++ [z] := by
        intro hm'
        have := hb next hm'
        omega
      obtain ⟨st', hs', ht'⟩ := hfin next (ys ++ [z]) hm (by simp; omega) hn (by omega)
      exact ⟨next, st', Or.inr rfl, hs', ht'⟩

/-- The first output `r+1` (zero-based `Q_1`) reads `0,...,r` into an empty
stack. Its batch fixes a bottom token `z < r` at depth `r`. -/
theorem first_record {r limit : Nat} {out : List Nat} (hr : 1 ≤ r)
    (h : RangeLazyRun r r limit 0 [] ((r+1) :: out)) :
    ∃ z st, z < r ∧ Shape z r (r+2) st ∧ RangeLazyRun r r limit (r+2) st out := by
  rcases h.cons_cases with ⟨after, pop, tail⟩ |
    ⟨before, after, lower, upper, fresh, read, pop, tail⟩
  · have hm := Step.pop_mem' pop
    simp at hm
  · have hread : Run r r [] (List.range' 0 (r+2)) [] before := by
      have hc : r+1+1-0 = r+2 := by omega
      simpa [hc] using read
    obtain ⟨ys, z, hb, hl, hz, hzr, hbd⟩ := initial_read hr (by omega) hread
    have hbound : ∀ x ∈ after, x < r+2 := by
      intro x hx
      rcases pop.mem_after hx with hx | hx
      · exact hbd x hx
      · simp at hx
    rw [hb] at pop
    obtain ⟨ys', ha, hl', hz'⟩ := pop_above_bottom pop (by omega) hz
    exact ⟨z, after, hzr, ⟨ys', ha, by omega, hz', hbound⟩, tail⟩

theorem lowSeg_snoc (r c : Nat) :
    lowSeg r 0 (c+1+1) = lowSeg r 0 (c+1) ++ [r+1+2*(c+1), c+1] := by
  rw [← lowSeg_append r 0 (c+1) 1]
  simp [lowSeg]

/-- The low phase `Q_0,0,...,Q_c,c` (zero-based). Afterwards the bottom token
is below `r`, differs from every low output so far, and has `r-1` tokens
above it. -/
theorem low_phase {r limit : Nat} (hr : 2 ≤ r) :
    ∀ c, c + 1 ≤ r - 1 → ∀ out,
      RangeLazyRun r r limit 0 [] (lowSeg r 0 (c+1) ++ out) →
      ∃ z st, z < r ∧ (∀ i, i ≤ c → z ≠ i) ∧ Shape z (r-1) (r+2*(c+1)) st ∧
        RangeLazyRun r r limit (r+2*(c+1)) st out := by
  intro c
  induction c with
  | zero =>
    intro _ out h
    have h₀ : RangeLazyRun r r limit 0 [] ((r+1) :: 0 :: out) := by
      simpa [lowSeg] using h
    obtain ⟨z, st, hzr, hs, ht⟩ := first_record (by omega) h₀
    have hz0 : z ≠ 0 := by
      intro he
      subst he
      have := hs.held_bottom ht
      omega
    obtain ⟨st₁, hs₁, h₁⟩ := hs.held_other (by omega) (Ne.symm hz0) ht
    refine ⟨z, st₁, hzr, ?_, ?_, h₁⟩
    · intro i hi; omega
    · simpa using hs₁
  | succ c ih =>
    intro hk out h
    rw [lowSeg_snoc, List.append_assoc] at h
    obtain ⟨z, st, hzr, hne, hs, ht⟩ := ih (by omega) _ h
    simp only [List.cons_append, List.nil_append] at ht
    obtain ⟨st₁, hs₁, h₁⟩ := hs.record (by omega) (by omega) ht
    have hd : r - 1 + (r+1+2*(c+1) - (r+2*(c+1))) = r := by omega
    have hn : r+1+2*(c+1)+1 = r+2*(c+1+1) := by omega
    rw [hd, hn] at hs₁
    rw [hn] at h₁
    have hzk : z ≠ c+1 := by
      intro he
      subst he
      have := hs₁.held_bottom h₁
      omega
    obtain ⟨st₂, hs₂, h₂⟩ := hs₁.held_other (by omega) (Ne.symm hzk) h₁
    refine ⟨z, st₂, hzr, ?_, by simpa using hs₂, h₂⟩
    intro i hi
    by_cases hik : i ≤ c
    · exact hne i hik
    · have : i = c+1 := by omega
      subst this
      exact hzk

/-- Lemma 4.1: after the whole prefix, `C = 3r-2` is the bottom token at
depth `r-2`, and the next unread value is `a_0 = 3r+3`. -/
theorem prefix_shape {r limit : Nat} (hr : 3 ≤ r) {out : List Nat}
    (h : RangeLazyRun r r limit 0 [] (lowSeg r 0 (r-1) ++ (prefixTail r ++ out))) :
    ∃ st, Shape (3*r-2) (r-2) (3*r+3) st ∧ RangeLazyRun r r limit (3*r+3) st out := by
  have hc : r - 2 + 1 = r - 1 := by omega
  rw [← hc] at h
  obtain ⟨z, st, hzr, hne, hs, ht⟩ := low_phase (by omega) (r-2) (by omega) _ h
  have hz : z = r - 1 := by
    by_cases hz : z ≤ r - 2
    · exact absurd rfl (hne z hz)
    · omega
  subst hz
  have hn : r+2*(r-2+1) = 3*r-2 := by omega
  rw [hn] at hs ht
  simp only [prefixTail, List.cons_append] at ht
  -- E_0
  obtain ⟨st₁, hs₁, h₁⟩ := hs.held_other (by omega) (by omega) ht
  -- M1 reads C and U: C must go below P
  obtain ⟨w, st₂, hw, hs₂, h₂⟩ := record_split hs₁ (by omega) (by omega) h₁
  have hd₂ : r - 1 - 1 + (3*r - (3*r-2)) = r := by omega
  rw [hd₂] at hs₂
  rcases hw with rfl | rfl
  · have := hs₂.held_bottom h₂
    omega
  -- P, then M2 reads V
  obtain ⟨st₃, hs₃, h₃⟩ := hs₂.held_other (by omega) (by omega) h₂
  obtain ⟨st₄, hs₄, h₄⟩ := hs₃.record (by omega) (by omega) h₃
  have hd₄ : r - 1 + (3*r+2 - (3*r+1)) = r := by omega
  have hn₄ : 3*r+2+1 = 3*r+3 := by omega
  rw [hd₄, hn₄] at hs₄
  rw [hn₄] at h₄
  -- U and E_1
  obtain ⟨st₅, hs₅, h₅⟩ := hs₄.held_other (by omega) (by omega) h₄
  obtain ⟨st₆, hs₆, h₆⟩ := hs₅.held_other (by omega) (by omega) h₅
  have hd₆ : r - 1 - 1 = r - 2 := by omega
  rw [hd₆] at hs₆
  exact ⟨st₆, hs₆, h₆⟩

theorem qv_lt (r j : Nat) (hr : 3 ≤ r) : qv r j < 3*r+3+3*j := by
  rcases qv_cases r j with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem qv_ne_C (r j : Nat) (hr : 3 ≤ r) : qv r j ≠ 3*r-2 := by
  rcases qv_cases r j with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- Lemma 4.2, iterated: each step keeps `C` at the bottom at depth `r-2`. -/
theorem step_phase {r limit : Nat} (hr : 3 ≤ r) :
    ∀ c j {st : List Nat} (out : List Nat), Shape (3*r-2) (r-2) (3*r+3+3*j) st →
      RangeLazyRun r r limit (3*r+3+3*j) st (stepSeg r j c ++ out) →
      ∃ st', Shape (3*r-2) (r-2) (3*r+3+3*(j+c)) st' ∧
        RangeLazyRun r r limit (3*r+3+3*(j+c)) st' out := by
  intro c
  induction c with
  | zero => intro j st out hs h; exact ⟨st, hs, by simpa [stepSeg] using h⟩
  | succ c ih =>
    intro j st out hs h
    rw [stepSeg_succ, List.append_assoc] at h
    simp only [List.cons_append, List.nil_append] at h
    obtain ⟨w, st₁, hw, hs₁, h₁⟩ := record_split hs (by omega) (by omega) h
    have hd₁ : r - 2 + (3*r+5+3*j - (3*r+3+3*j)) = r := by omega
    rw [hd₁] at hs₁
    rcases hw with rfl | rfl
    · obtain ⟨st₂, hs₂, h₂⟩ := hs₁.held_other (by omega) (by omega) h₁
      obtain ⟨st₃, hs₃, h₃⟩ := hs₂.held_other
        (by have := qv_lt r j hr; omega) (qv_ne_C r j hr) h₂
      have hn : 3*r+5+3*j+1 = 3*r+3+3*(j+1) := by omega
      rw [hn] at hs₃ h₃
      have hd : r - 1 - 1 = r - 2 := by omega
      rw [hd] at hs₃
      obtain ⟨st₄, hs₄, h₄⟩ := ih (j+1) out hs₃ h₃
      have he : j + 1 + c = j + (c+1) := by omega
      rw [he] at hs₄ h₄
      exact ⟨st₄, hs₄, h₄⟩
    · have := hs₁.held_bottom h₁
      omega

/-- No unrestricted original `(r,r)` history generates `A_r(k)`. -/
theorem famA_not_generated (r k : Nat) (hr : 3 ≤ r) :
    ¬ Run r r [] (List.range (3*r+7+3*k)) (famA r k) [] := by
  intro h
  have hl := generated_rangeLazy h
  simp only [famA] at hl
  obtain ⟨st, hs, ht⟩ := prefix_shape hr hl
  obtain ⟨st₁, hs₁, h₁⟩ := step_phase hr k 0 _ (by simpa using hs) (by simpa using ht)
  simp only [Nat.zero_add] at hs₁ h₁
  -- the record a+3 reads a, a+1, a+2
  obtain ⟨w, st₂, hw, hs₂, h₂⟩ := record_split hs₁ (by omega) (by omega) h₁
  have hd₂ : r - 2 + (3*r+6+3*k - (3*r+3+3*k)) = r + 1 := by omega
  rw [hd₂] at hs₂
  rcases hw with rfl | rfl
  · obtain ⟨st₃, hs₃, h₃⟩ := hs₂.held_other (by omega) (by omega) h₂
    have := hs₃.held_bottom h₃
    omega
  · have := hs₂.held_bottom h₂
    omega

/-- No unrestricted original `(r,r)` history generates `B_r(k)`. -/
theorem famB_not_generated (r k : Nat) (hr : 3 ≤ r) :
    ¬ Run r r [] (List.range (3*r+8+3*k)) (famB r k) [] := by
  intro h
  have hl := generated_rangeLazy h
  simp only [famB] at hl
  obtain ⟨st, hs, ht⟩ := prefix_shape hr hl
  obtain ⟨st₁, hs₁, h₁⟩ := step_phase hr k 0 _ (by simpa using hs) (by simpa using ht)
  simp only [Nat.zero_add] at hs₁ h₁
  -- the record a+2 reads a, a+1
  obtain ⟨w, st₂, hw, hs₂, h₂⟩ := record_split hs₁ (by omega) (by omega) h₁
  have hd₂ : r - 2 + (3*r+5+3*k - (3*r+3+3*k)) = r := by omega
  rw [hd₂] at hs₂
  rcases hw with rfl | rfl
  · obtain ⟨st₃, hs₃, h₃⟩ := hs₂.held_other (by omega) (by omega) h₂
    -- the record a+4 reads a+3, which lands above C
    obtain ⟨st₄, hs₄, h₄⟩ := hs₃.record (by omega) (by omega) h₃
    have hd₄ : r - 1 + (3*r+7+3*k - (3*r+5+3*k+1)) = r := by omega
    rw [hd₄] at hs₄
    have := hs₄.held_bottom h₄
    omega
  · have := hs₂.held_bottom h₂
    omega

theorem famA_no_executable_trace (r k : Nat) (hr : 3 ≤ r) :
    ¬ ∃ ops, run r r ops [] = some ([], famA r k) ∧ inputs ops = List.range (3*r+7+3*k) := by
  rw [← run_relational_iff]
  exact famA_not_generated r k hr

theorem famB_no_executable_trace (r k : Nat) (hr : 3 ≤ r) :
    ¬ ∃ ops, run r r ops [] = some ([], famB r k) ∧ inputs ops = List.range (3*r+8+3*k) := by
  rw [← run_relational_iff]
  exact famB_not_generated r k hr

#print axioms record_split
#print axioms prefix_shape
#print axioms step_phase
#print axioms famA_not_generated
#print axioms famB_not_generated
#print axioms famA_no_executable_trace
#print axioms famB_no_executable_trace
end Equal
end StackSorting.Generalized
