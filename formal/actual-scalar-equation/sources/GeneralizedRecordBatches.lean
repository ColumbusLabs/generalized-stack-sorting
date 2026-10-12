import GeneralizedCompletionCodes

/-! Unbounded record-batch successor semantics for the exact completion code
language. The record outputs its last fresh token, so only b-1 are appended. -/
namespace StackSorting.Generalized.Decorated
open LazyCode

def appendHeld (state : State) : Nat → State
  | 0 => state
  | count+1 => appendHeld (push state) count

theorem height_push (state : State) : height (push state) = height state+1 := by
  have hh : (pushFactor (height state)).height = 1 := by
    unfold pushFactor
    split <;> (try split) <;> rfl
  change ((state ++ [pushFactor (height state)]).map Factor.height).sum = height state+1
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hh]
  rfl

theorem height_appendHeld (state : State) (count : Nat) :
    height (appendHeld state count) = height state+count := by
  induction count generalizing state with
  | zero => simp [appendHeld]
  | succ count ih => simp [appendHeld, ih, height_push, Nat.add_assoc, Nat.add_comm ]

theorem appendHeld_valid {state : State} (valid : Valid state) (count : Nat) :
    Valid (appendHeld state count) := by
  induction count generalizing state with
  | zero => exact valid
  | succ count ih => exact ih (push_valid valid)

/-- Arbitrarily long record appends agree with literal physical rank pushes. -/
theorem appendHeld_represents (state : State) (count : Nat) (after : List Nat) :
    Represents (appendHeld state count) after ↔
      ∃ physical, Represents state physical ∧
        after ∈ rankReadOrders 3 (height state) count physical := by
  induction count generalizing state with
  | zero => simp [appendHeld, rankReadOrders]
  | succ count ih =>
    rw [appendHeld, ih]
    constructor
    · rintro ⟨middle, hm, ha⟩
      obtain ⟨physical, hp, hpush⟩ := (push_represents_iff state middle).mp hm
      refine ⟨physical, hp, ?_⟩
      simp only [rankReadOrders, List.mem_flatMap]
      exact ⟨middle, mem_pushOrders_iff.mpr hpush, by simpa [height_push] using ha⟩
    · rintro ⟨physical, hp, ha⟩
      obtain ⟨middle, hm, ht⟩ := List.mem_flatMap.mp ha
      exact ⟨middle, (push_represents_iff state middle).mpr
        ⟨physical, hp, mem_pushOrders_iff.mp hm⟩, by simpa [height_push] using ht⟩

/-- Exact first-record successor, including the zero- and one-held-token
boundary rules and all positive batch sizes. -/
theorem codeCompletion_record_target (state : State) (n b : Nat) (code : List Letter) :
    CodeCompletion state n (.N b :: code) ↔
      0 < b ∧ b ≤ n ∧ CodeCompletion (appendHeld state (b-1)) (n-b) code := by
  rw [codeCompletion_record]
  constructor
  · rintro ⟨positive, valid, budget, physical, after, hp, hr, ha⟩
    have hh : height (appendHeld state (b-1)) = height state+b-1 := by
      rw [height_appendHeld]; omega
    exact ⟨positive, valid, by simpa [hh] using budget, after,
      (appendHeld_represents state (b-1) after).mpr ⟨physical, hp, hr⟩,
      by simpa [hh] using ha⟩
  · rintro ⟨positive, valid, budget, after, hp, ha⟩
    have hh : height (appendHeld state (b-1)) = height state+b-1 := by
      rw [height_appendHeld]; omega
    obtain ⟨physical, hp, hr⟩ := (appendHeld_represents state (b-1) after).mp hp
    exact ⟨positive, valid, by simpa [hh] using budget, physical, after, hp, hr,
      by simpa [hh] using ha⟩

#print axioms appendHeld_represents
#print axioms codeCompletion_record_target
end StackSorting.Generalized.Decorated
