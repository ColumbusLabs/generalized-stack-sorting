import RankBlockTransitions

namespace StackSorting.Generalized

variable {α : Type}

theorem pushOrder_one_iff (xs : List Nat) : PushOrder 1 xs ↔ xs = [0] := by
  constructor
  · intro h
    cases h with
    | top h => cases h; rfl
    | second h => cases h
  · rintro rfl; exact PushOrder.nil.top

theorem pushOrder_two_iff (xs : List Nat) :
    PushOrder 2 xs ↔ xs = [0,1] ∨ xs = [1,0] := by
  constructor
  · intro h
    cases h with
    | top h =>
        have he := (pushOrder_one_iff _).mp h
        simp [he]
    | second h =>
        have he := (pushOrder_one_iff _).mp h
        simp only [List.cons.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        simp
  · rintro (rfl | rfl)
    · exact PushOrder.nil.top.second
    · exact PushOrder.nil.top.top

theorem pushOrder_three_iff (xs : List Nat) :
    PushOrder 3 xs ↔ xs = [0,2,1] ∨ xs = [2,0,1] ∨
      xs = [1,2,0] ∨ xs = [2,1,0] := by
  constructor
  · intro h
    cases h with
    | top h =>
        rcases (pushOrder_two_iff _).mp h with he | he <;> simp [he]
    | second h =>
        rcases (pushOrder_two_iff _).mp h with he | he
        all_goals simp only [List.cons.injEq] at he
        all_goals rcases he with ⟨rfl, rfl⟩; simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact PushOrder.nil.top.second.second
    · exact PushOrder.nil.top.second.top
    · exact PushOrder.nil.top.top.second
    · exact PushOrder.nil.top.top.top

theorem rankBlock_one_iff (f : Nat → α) (xs : List α) :
    RankBlock f 0 1 xs ↔ xs = [f 0] := by
  constructor
  · rintro ⟨ranks, hr, rfl⟩
    have he := (pushOrder_one_iff _).mp ((segmentOrder_zero _ _).mp hr).push
    simp [he]
  · rintro rfl
    exact ⟨[0], (segmentOrder_zero _ _).mpr PushOrder.nil.top.interval, rfl⟩

theorem rankBlock_two_iff (f : Nat → α) (xs : List α) :
    RankBlock f 0 2 xs ↔ xs = [f 0,f 1] ∨ xs = [f 1,f 0] := by
  constructor
  · rintro ⟨ranks, hr, rfl⟩
    rcases (pushOrder_two_iff _).mp ((segmentOrder_zero _ _).mp hr).push with he | he <;>
      simp [he]
  · rintro (rfl | rfl)
    · exact ⟨[0,1], (segmentOrder_zero _ _).mpr PushOrder.nil.top.second.interval, rfl⟩
    · exact ⟨[1,0], (segmentOrder_zero _ _).mpr PushOrder.nil.top.top.interval, rfl⟩

theorem rankBlock_three_iff (f : Nat → α) (xs : List α) :
    RankBlock f 0 3 xs ↔ xs = [f 0,f 2,f 1] ∨ xs = [f 2,f 0,f 1] ∨
      xs = [f 1,f 2,f 0] ∨ xs = [f 2,f 1,f 0] := by
  constructor
  · rintro ⟨ranks, hr, rfl⟩
    rcases (pushOrder_three_iff _).mp ((segmentOrder_zero _ _).mp hr).push with
      he | he | he | he <;> simp [he]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨[0,2,1], (segmentOrder_zero _ _).mpr
        PushOrder.nil.top.second.second.interval, rfl⟩
    · exact ⟨[2,0,1], (segmentOrder_zero _ _).mpr
        PushOrder.nil.top.second.top.interval, rfl⟩
    · exact ⟨[1,2,0], (segmentOrder_zero _ _).mpr
        PushOrder.nil.top.top.second.interval, rfl⟩
    · exact ⟨[2,1,0], (segmentOrder_zero _ _).mpr
        PushOrder.nil.top.top.top.interval, rfl⟩

#print axioms rankBlock_one_iff
#print axioms rankBlock_two_iff
#print axioms rankBlock_three_iff
end StackSorting.Generalized
