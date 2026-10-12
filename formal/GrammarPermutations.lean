import FiniteWords
import CompleteGrammar

/-! # Exact size-preserving grammar/permutation bridge

The first-return grammar is connected here to the independently defined
original no-bypass stack machine and its duplicate-free finite enumerations.
-/
namespace StackSorting.FirstReturn
open StackSorting

theorem wordWeight_eq (ops : List Op) : wordWeight ops = Labelled.weight ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    have hw : opWeight op = Labelled.opWeight op := by cases op <;> rfl
    simpa [wordWeight, Labelled.weight, hw] using congrArg (opWeight op + ·) ih

theorem accepted_path (p : Path) (hp : Valid p) :
    Labelled.AcceptedWord (pathWeight p) (pathEncode p) := by
  constructor
  · exact (accepts_iff _).mpr ⟨true, path_sound p hp⟩
  · rw [← wordWeight_eq, pathEncode_weight]

/-- At fixed size, every accepted word has one and only one valid grammar parse. -/
theorem accepted_iff_sized_grammar (n : Nat) (ops : List Op) :
    Labelled.AcceptedWord n ops ↔
      ∃ p, Valid p ∧ pathWeight p = n ∧ pathEncode p = ops := by
  constructor
  · rintro ⟨ha, hw⟩
    obtain ⟨p, ⟨hp, he⟩, _⟩ := (accepted_iff_unique_grammar ops).mp ((accepts_iff ops).mp ha)
    refine ⟨p, hp, ?_, he⟩
    rw [← pathEncode_weight, he, wordWeight_eq, hw]
  · rintro ⟨p, hp, hw, rfl⟩
    simpa [hw] using accepted_path p hp

def permutation (p : Path) : List Nat := Labelled.decode (pathEncode p)

theorem permutation_sound (p : Path) (hp : Valid p) :
    Labelled.CanSort [] (permutation p) (List.range' 1 (pathWeight p)) :=
  Labelled.decode_sound _ _ (accepted_path p hp)

theorem permutation_injective (p q : Path) (hp : Valid p) (hq : Valid q)
    (hw : pathWeight p = pathWeight q) (he : permutation p = permutation q) : p = q := by
  apply pathEncode_injective
  exact Labelled.decode_injective (pathWeight p) _ _ (accepted_path p hp)
    (by simpa [hw] using accepted_path q hq) he

theorem permutation_surjective (n : Nat) (input : List Nat)
    (hs : Labelled.CanSort [] input (List.range' 1 n)) :
    ∃ p, Valid p ∧ pathWeight p = n ∧ permutation p = input := by
  obtain ⟨ops, ha, he⟩ := Labelled.decode_surjective n input hs
  obtain ⟨p, hp, hw, hew⟩ := (accepted_iff_sized_grammar n ops).mp ha
  exact ⟨p, hp, hw, by simpa [permutation, hew] using he⟩

/-- The explicit finite word enumeration indexes exactly the valid size-n
first-return paths, without quotienting parallel operation labels. -/
theorem mem_acceptedWords_iff (n : Nat) (ops : List Op) :
    ops ∈ Labelled.acceptedWords n ↔
      ∃ p, Valid p ∧ pathWeight p = n ∧ pathEncode p = ops :=
  (Labelled.mem_acceptedWords n ops).trans (accepted_iff_sized_grammar n ops)

#print axioms accepted_iff_sized_grammar
#print axioms permutation_sound
#print axioms permutation_injective
#print axioms permutation_surjective
#print axioms mem_acceptedWords_iff
end StackSorting.FirstReturn
