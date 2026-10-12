import GeneralizedUnaryBoundary

namespace StackSorting.Generalized.Decorated
namespace UnarySuffix
open Coordinates ExceptionalSuffix

theorem build_exists_bounded {digits held : List Nat} {next : Nat}
    (hb : ∀ digit ∈ digits, digit < 3) (hh : 2 ≤ held.length) :
    ∃ after, build next digits held = some after := by
  induction digits generalizing held next with
  | nil => exact ⟨held, rfl⟩
  | cons slot digits ih =>
    have hs := hb slot (by simp)
    obtain ⟨middle, hm⟩ := exists_insertAt (slot := slot) (token := next) (held := held) (by omega)
    have hlen := insertAt_length slot next held middle hm
    obtain ⟨after, ha⟩ := ih (held := middle) (next := next+1) (fun digit hd => hb digit (by simp [hd])) (by omega)
    refine ⟨after, ?_⟩
    change (insertAt? slot next held).bind (fun after => build (next+1) digits after) = some after
    rw [hm]
    exact ha

theorem decodes_after_two {slot : Nat} {digits : List Nat}
    (hs : slot ≤ 1) (hb : ∀ digit ∈ digits, digit < 3) :
    ∃ after, Coordinates.Decodes (0 :: slot :: digits) after := by
  obtain ⟨middle, hm⟩ := exists_insertAt (slot := slot) (token := 2) (held := [1]) (by simpa using hs)
  have hlen := insertAt_length slot 2 [1] middle hm
  obtain ⟨after, ha⟩ := build_exists_bounded (next := 3) (held := middle) hb (by simp only [List.length_cons, List.length_nil] at hlen; omega)
  refine ⟨after, ?_⟩
  change (insertAt? slot 2 [1]).bind (fun middle => build 3 digits middle) = some after
  rw [hm]
  exact ha

/-- The explicit graph boundary forms are genuine coordinate-valid unary
states for arbitrarily long suffixes, without a finite held-height cutoff. -/
theorem boundary_valid {state : State} (hb : Boundary state) : Valid state := by
  rcases hb with rfl | rfl | ⟨factor, rest, hf, rfl, _⟩
  · exact empty_valid
  · intro digits hd
    have he : digits = [0] := (denotes_single .Z digits).mp hd
    subst digits
    exact ⟨[1], rfl⟩
  · intro digits hd
    obtain ⟨tail, ht, rfl⟩ := (denotes_Z _ _).mp hd
    rcases hf with rfl | rfl
    · obtain ⟨after, ha, rfl⟩ := (denotes_Z _ _).mp ht
      exact decodes_after_two (by omega) (denotes_bounded ha)
    · obtain ⟨slot, after, hs, ha, rfl⟩ := (denotes_B _ _).mp ht
      have hslot : slot ≤ 1 := by rcases hs with rfl | rfl <;> omega
      exact decodes_after_two hslot (denotes_bounded ha)

theorem valid_iff_boundary {state : State} (ht : ThreeLetters state) :
    Valid state ↔ Boundary state := ⟨valid_unary_boundary ht, boundary_valid⟩

#print axioms boundary_valid
end UnarySuffix
end StackSorting.Generalized.Decorated
