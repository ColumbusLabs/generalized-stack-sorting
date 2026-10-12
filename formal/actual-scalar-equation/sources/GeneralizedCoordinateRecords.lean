import GeneralizedCoordinateDeletion
import GeneralizedCodeRecognition

/-! Exact unrestricted record transitions in maximum-insertion coordinates.
This connects the physical subset recognizer already proved equivalent to
actual generated permutations to the coordinate decoder, before any compact
factor language or counting quotient is introduced. -/
namespace StackSorting.Generalized
namespace Coordinates
open LazyCode

/-- The literal subset recognizer's increasing-input push block is exactly
the union of bounded-coordinate decodings. Duplicate coordinate witnesses
are used only existentially, never as counting multiplicities. -/
theorem readOrders_build_iff (r next n : Nat) (held after : List Nat) :
    after ∈ readOrders r (List.range' next n) held ↔
      ∃ digits, digits.length = n ∧ (∀ slot ∈ digits, slot < r) ∧
        build next digits held = some after := by
  induction n generalizing next held with
  | zero =>
    constructor
    · intro hm
      have he : after = held := by simpa [readOrders] using hm
      subst after
      exact ⟨[], rfl, by simp, rfl⟩
    · rintro ⟨digits, hl, _, hb⟩
      have he : digits = [] := List.length_eq_zero_iff.mp hl
      subst digits
      simpa [build, readOrders] using hb.symm
  | succ n ih =>
    constructor
    · intro hm
      have hm' : ∃ middle, middle ∈ pushOrders r next held ∧
          after ∈ readOrders r (List.range' (next+1) n) middle := by
        simpa [List.range'_succ, readOrders, List.mem_flatMap] using hm
      obtain ⟨middle, hpush, htail⟩ := hm'
      obtain ⟨slot, hslot, hi⟩ := List.mem_filterMap.mp hpush
      obtain ⟨digits, hl, hd, hb⟩ := (ih (next+1) middle).mp htail
      refine ⟨slot :: digits, by simp [hl], ?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_range.mp hslot
        · exact hd a ha
      · simp [build, hi, hb]
    · rintro ⟨digits, hl, hd, hb⟩
      cases digits with
      | nil => simp at hl
      | cons slot digits =>
        have hlen : digits.length = n := by simpa using hl
        have hslot : slot < r := hd slot (by simp)
        have htail : ∀ a ∈ digits, a < r := fun a ha => hd a (by simp [ha])
        cases hi : insertAt? slot next held with
        | none => simp [build, hi] at hb
        | some middle =>
          have hb' : build (next+1) digits middle = some after := by
            simpa [build, hi] using hb
          have hm : middle ∈ pushOrders r next held :=
            List.mem_filterMap.mpr ⟨slot, List.mem_range.mpr hslot, hi⟩
          have ht := (ih (next+1) middle).mpr ⟨digits, hlen, htail, hb'⟩
          simpa [List.range'_succ, readOrders, List.mem_flatMap] using
            (show ∃ mid, mid ∈ pushOrders r next held ∧
              after ∈ readOrders r (List.range' (next+1) n) mid from ⟨middle, hm, ht⟩)

/-- Both directions of the record shortcut are now proved for coordinate
words: an N_b consumes b input labels but appends exactly b-1 held digits. -/
theorem record_batch_coordinates_iff {r s next b : Nat} {held after : List Nat}
    (hr : 0 < r) (hs : 0 < s) (hb : 0 < b)
    (old : ∀ token ∈ held, token < next) :
    (∃ before, Run r s held (List.range' next b) [] before ∧
      Step r s before [] [next+b-1] after) ↔
    ∃ digits, digits.length = b-1 ∧ (∀ slot ∈ digits, slot < r) ∧
      build next digits held = some after :=
  (record_transition_iff hr hs hb old).symm.trans
    (readOrders_build_iff r next (b-1) held after)

/-- The record part of the unrestricted top-three coordinate-state model. -/
theorem three_three_record_coordinates_iff {next b : Nat} {held after : List Nat}
    (hb : 0 < b) (old : ∀ token ∈ held, token < next) :
    (∃ before, Run 3 3 held (List.range' next b) [] before ∧
      Step 3 3 before [] [next+b-1] after) ↔
    ∃ digits, digits.length = b-1 ∧ (∀ slot ∈ digits, slot < 3) ∧
      build next digits held = some after :=
  record_batch_coordinates_iff (by decide) (by decide) hb old

#print axioms readOrders_build_iff
#print axioms record_batch_coordinates_iff
#print axioms three_three_record_coordinates_iff
end Coordinates
end StackSorting.Generalized
