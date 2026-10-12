import GeneralizedUnaryTargetShape
import GeneralizedRecordBatches

/-! The exact low-height boundary domain of unary physical coordinate states.
Validity, rather than an assumed normal form, forces the Z and Z/B prefix. -/
namespace StackSorting.Generalized.Decorated
namespace UnarySuffix
open Coordinates

def Boundary (state : State) : Prop :=
  state = [] ∨ state = [.Z] ∨ ∃ factor rest,
    (factor = .Z ∨ factor = .B) ∧ state = .Z :: factor :: rest ∧ ThreeLetters rest

theorem valid_unary_first {factor : Factor} {rest : State}
    (ht : ThreeLetters (factor :: rest)) (hv : Valid (factor :: rest)) : factor = .Z := by
  obtain ⟨digits, hd⟩ := ht.tail.inhabited
  rcases ht factor (by simp) with hz | hb | ht
  · exact hz
  · subst factor
    obtain ⟨physical, hp⟩ := hv (1 :: digits) ⟨[1], digits, Or.inr rfl, hd, rfl⟩
    simp [Coordinates.Decodes, build, insertAt?] at hp
  · subst factor
    obtain ⟨physical, hp⟩ := hv (1 :: digits) ⟨[1], digits, Or.inr (Or.inl rfl), hd, rfl⟩
    simp [Coordinates.Decodes, build, insertAt?] at hp

theorem valid_unary_second {factor : Factor} {rest : State}
    (ht : ThreeLetters (.Z :: factor :: rest)) (hv : Valid (.Z :: factor :: rest)) :
    factor = .Z ∨ factor = .B := by
  rcases ht factor (by simp) with hz | hb | hf
  · exact Or.inl hz
  · exact Or.inr hb
  · subst factor
    obtain ⟨digits, hd⟩ := ht.tail.tail.inhabited
    have hword : denotes (.Z :: .T :: rest) (0 :: 2 :: digits) :=
      ⟨[0], 2 :: digits, rfl, ⟨[2], digits, Or.inr (Or.inr rfl), hd, rfl⟩, rfl⟩
    obtain ⟨physical, hp⟩ := hv _ hword
    simp [Coordinates.Decodes, build, insertAt?] at hp

/-- All valid unary states are exactly in the graph certificate's required
empty, singleton-Z, ZB-word or ZZ-word boundary families. -/
theorem valid_unary_boundary {state : State} (ht : ThreeLetters state) (hv : Valid state) :
    Boundary state := by
  cases state with
  | nil => exact Or.inl rfl
  | cons factor rest =>
    have hf := valid_unary_first ht hv
    subst factor
    cases rest with
    | nil => exact Or.inr (Or.inl rfl)
    | cons second rest =>
      exact Or.inr (Or.inr ⟨second, rest, valid_unary_second ht hv, rfl, ht.tail.tail⟩)

theorem threeLetters_push {state : State} (ht : ThreeLetters state) : ThreeLetters (push state) := by
  apply threeLetters_append ht
  apply threeLetters_single
  unfold pushFactor
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem threeLetters_appendHeld {state : State} (ht : ThreeLetters state) (count : Nat) :
    ThreeLetters (appendHeld state count) := by
  induction count generalizing state with
  | zero => exact ht
  | succ count ih => exact ih (threeLetters_push ht)

#print axioms valid_unary_boundary
#print axioms threeLetters_appendHeld
end UnarySuffix
end StackSorting.Generalized.Decorated
