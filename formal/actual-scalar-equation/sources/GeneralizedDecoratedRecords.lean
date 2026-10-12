import GeneralizedDecoratedSemantics

/-! Exact normal-form record appends. The three initial-height cases are
proved against actual physical insertions, not chosen by a counting contract. -/
namespace StackSorting.Generalized
namespace Decorated
open Coordinates LazyCode

def pushFactor (h : Nat) : Factor := if h = 0 then .Z else if h = 1 then .B else .T

def push (state : State) : State := state ++ [pushFactor (height state)]

theorem pushFactor_singleton (h : Nat) (digits : List Nat) :
    (pushFactor h).denotes digits ↔
      ∃ slot, digits = [slot] ∧ slot < 3 ∧ slot ≤ h := by
  by_cases hz : h = 0
  · subst h
    simp [pushFactor, Factor.denotes]
  · by_cases ho : h = 1
    · subst h
      simp only [pushFactor, Nat.one_ne_zero, ite_false, ite_true, Factor.denotes]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, rfl, by omega, by omega⟩
        · exact ⟨1, rfl, by omega, by omega⟩
      · rintro ⟨slot, rfl, _, hs⟩
        have hcase : slot = 0 ∨ slot = 1 := by omega
        rcases hcase with rfl | rfl <;> simp
    · simp only [pushFactor, hz, ho, ite_false, Factor.denotes]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, rfl, by omega, by omega⟩
        · exact ⟨1, rfl, by omega, by omega⟩
        · exact ⟨2, rfl, by omega, by omega⟩
      · rintro ⟨slot, rfl, hs, _⟩
        have hcase : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
        rcases hcase with rfl | rfl | rfl <;> simp

theorem denotes_one_factor (factor : Factor) (digits : List Nat) :
    denotes [factor] digits ↔ factor.denotes digits := by simp [denotes]

theorem exists_insertAt {slot token : Nat} {held : List Nat} (h : slot ≤ held.length) :
    ∃ after, insertAt? slot token held = some after := by
  have hp : (held.take slot).length = slot := by simp [List.length_take, Nat.min_eq_left h]
  exact ⟨held.take slot ++ token :: held.drop slot,
    by simpa [hp] using insertAt_prefix (held.take slot) (held.drop slot) token⟩

/-- One normal-form append represents exactly every legal physical push of
the next maximum, including the special zero- and one-held-token boundaries. -/
theorem push_represents_iff (state : State) (after : List Nat) :
    Represents (push state) after ↔
      ∃ physical, Represents state physical ∧
        Step 3 3 physical [height state+1] [] after := by
  constructor
  · rintro ⟨digits, hd, hb⟩
    obtain ⟨oldDigits, freshDigits, ho, hf, rfl⟩ := (denotes_append _ _ _).mp hd
    obtain ⟨slot, rfl, hs, _⟩ := (pushFactor_singleton _ _).mp
      ((denotes_one_factor _ _).mp hf)
    unfold Coordinates.Decodes at hb
    rw [build_append] at hb
    cases hc : build 1 oldDigits [] with
    | none => simp [hc] at hb
    | some physical =>
      have hi : insertAt? slot (height state+1) physical = some after := by
        simpa [hc, build, denotes_length ho, Nat.add_comm] using hb
      exact ⟨physical, ⟨oldDigits, ho, hc⟩,
        step_relational 3 3 (.push slot (height state+1)) physical after []
          (by simp [step, hs, hi])⟩
  · rintro ⟨physical, ⟨oldDigits, ho, hb⟩, hp⟩
    cases hp with
    | push pre post token allowed =>
      have physicalLength : (pre ++ post).length = height state := by
        have hl := (Coordinates.Decodes.permutation hb).length_eq
        simpa [denotes_length ho] using hl
      have hl : pre.length ≤ height state := by simp only [List.length_append] at physicalLength; omega
      refine ⟨oldDigits ++ [pre.length], ?_, ?_⟩
      · apply (denotes_append _ _ _).mpr
        exact ⟨oldDigits, [pre.length], ho,
          (denotes_one_factor _ _).mpr ((pushFactor_singleton _ _).mpr
            ⟨pre.length, rfl, allowed, hl⟩), rfl⟩
      · unfold Coordinates.Decodes
        rw [build_append, hb]
        simp [build, denotes_length ho, Nat.add_comm, insertAt_prefix]

/-- Ambient coordinate validity is preserved by every record append. -/
theorem push_valid {state : State} (valid : Valid state) : Valid (push state) := by
  intro digits hd
  obtain ⟨oldDigits, freshDigits, ho, hf, rfl⟩ := (denotes_append _ _ _).mp hd
  obtain ⟨slot, rfl, _, hs⟩ := (pushFactor_singleton _ _).mp
    ((denotes_one_factor _ _).mp hf)
  obtain ⟨physical, hb⟩ := valid oldDigits ho
  have hl : physical.length = height state := by
    simpa [denotes_length ho] using hb.permutation.length_eq
  obtain ⟨after, hi⟩ := exists_insertAt (slot := slot) (held := physical) (token := height state+1) (by simpa [hl] using hs)
  refine ⟨after, ?_⟩
  unfold Coordinates.Decodes
  rw [build_append, hb]
  simpa [build, denotes_length ho, Nat.add_comm] using hi

theorem empty_valid : Valid [] := by
  intro digits hd
  have he : digits = [] := hd
  subst digits
  exact ⟨[], rfl⟩

#print axioms push_represents_iff
#print axioms push_valid
end Decorated
end StackSorting.Generalized
