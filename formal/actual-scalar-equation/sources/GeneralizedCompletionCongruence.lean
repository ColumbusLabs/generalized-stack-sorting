import GeneralizedCompletionCounting
import GeneralizedUnarySuffix

/-! Extensionality for actual distinct-output counts. Equal coordinate
languages have equal completion counts, with no supplied cardinality premise. -/
namespace StackSorting.Generalized.Decorated

theorem completionCount_of_no_coordinates {state : State} (hn : ∀ digits, ¬ denotes state digits)
    (n : Nat) : completionCount state n = 0 := by
  have hempty : completionOutputs state n = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro output hm
    obtain ⟨physical, ⟨digits, hd, _⟩, _⟩ := (mem_completionOutputs state n output).mp hm
    exact hn digits hd
  simp [completionCount, hempty]

theorem completionCount_language_congr {left right : State}
    (he : ∀ digits, denotes left digits ↔ denotes right digits) (n : Nat) :
    completionCount left n = completionCount right n := by
  classical
  by_cases hi : ∃ digits, denotes left digits
  · obtain ⟨digits, hd⟩ := hi
    have hh : height left = height right :=
      (denotes_length hd).symm.trans (denotes_length ((he digits).mp hd))
    have hrep (physical : List Nat) : Represents left physical ↔ Represents right physical := by
      unfold Represents
      exact exists_congr fun digits => and_congr (he digits) Iff.rfl
    have hc (output : List Nat) : Completion left n output ↔ Completion right n output := by
      unfold Completion
      rw [hh]
      exact exists_congr fun physical => and_congr (hrep physical) Iff.rfl
    have hp : (completionOutputs left n).Perm (completionOutputs right n) := by
      apply (List.perm_ext_iff_of_nodup (completionOutputs_nodup left n)
        (completionOutputs_nodup right n)).mpr
      intro output
      rw [mem_completionOutputs, mem_completionOutputs]
      exact hc output
    exact hp.length_eq
  · have hl : ∀ digits, ¬ denotes left digits := fun digits hd => hi ⟨digits, hd⟩
    have hr : ∀ digits, ¬ denotes right digits := fun digits hd => hl digits ((he digits).mpr hd)
    rw [completionCount_of_no_coordinates hl, completionCount_of_no_coordinates hr]

namespace UnarySuffix

noncomputable def optionalCount (pre : State) (target : Option State) (n : Nat) : Int :=
  match target with
  | none => 0
  | some state => completionCount (pre ++ state) n

theorem prefixed_count_of_no_coordinates (pre state : State)
    (hn : ∀ digits, ¬ denotes state digits) (n : Nat) : completionCount (pre ++ state) n = 0 := by
  apply completionCount_of_no_coordinates
  intro digits hd
  obtain ⟨_, suffix, _, hs, _⟩ := (denotes_append pre state digits).mp hd
  exact hn suffix hs

theorem optionalCount_congr (pre : State) {left right : Option State}
    (he : ∀ digits, denoteOption left digits ↔ denoteOption right digits) (n : Nat) :
    optionalCount pre left n = optionalCount pre right n := by
  cases left with
  | none =>
    cases right with
    | none => rfl
    | some state =>
      have hn : ∀ digits, ¬ denotes state digits := fun digits hd => (he digits).mpr hd
      simp only [optionalCount, prefixed_count_of_no_coordinates pre state hn, Int.natCast_zero]
  | some state =>
    cases right with
    | none =>
      have hn : ∀ digits, ¬ denotes state digits := fun digits hd => (he digits).mp hd
      simp only [optionalCount, prefixed_count_of_no_coordinates pre state hn, Int.natCast_zero]
    | some target =>
      apply congrArg (fun count : Nat => (count : Int))
      apply completionCount_language_congr
      intro digits
      rw [denotes_append, denotes_append]
      exact exists_congr fun before => exists_congr fun after =>
        and_congr Iff.rfl (and_congr (he after) Iff.rfl)

theorem optionalCount_prepend (pre : State) (factor : Factor) (target : Option State) (n : Nat) :
    optionalCount pre (prepend factor target) n = optionalCount (pre ++ [factor]) target n := by
  cases target <;> simp [optionalCount, prepend, List.append_assoc]

#print axioms optionalCount_congr
end UnarySuffix
#print axioms completionCount_language_congr
end StackSorting.Generalized.Decorated
