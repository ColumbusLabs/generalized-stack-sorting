import GeneralizedCompletionCounting

/-! Identification of the empty-state completion count with the independently
reviewed actual distinct-permutation counting sequence, using canonical rank
codes so no label shift is silently assumed. -/
namespace StackSorting.Generalized.Decorated
open LazyCode ActualCounting

theorem represents_empty_iff (physical : List Nat) :
    Represents [] physical ↔ physical = [] := by
  simp [Represents, denotes, Coordinates.Decodes, Coordinates.build]

theorem empty_codeCompletion_iff (n : Nat) (code : List Letter) :
    CodeCompletion [] n code ↔ code ∈ acceptedCodes 3 3 n := by
  rw [mem_acceptedCodes_iff]
  constructor
  · rintro ⟨hb, physical, hp, ha⟩
    have hp' := (represents_empty_iff physical).mp hp
    subst physical
    have hlen : code.length = n := by simpa [height] using hb.length
    have hbound : Bounded n 0 code := by simpa [height] using hb.bounded (by simp [height])
    obtain ⟨output, hd, _, _⟩ := bounded_word_permutation hbound
    rw [hlen] at hd
    exact ⟨hlen, hbound, (hd.recognizes_iff (by decide) (by decide)).mpr
      ((hd.rankCodeOrders_iff_generated (by decide) (by decide)).mp ha)⟩
  · rintro ⟨hlen, hb, ha⟩
    obtain ⟨output, hd, _, _⟩ := bounded_word_permutation hb
    rw [hlen] at hd
    refine ⟨?_, [], (represents_empty_iff []).mpr rfl, ?_⟩
    · simpa [height] using hd.budget
    · exact (hd.rankCodeOrders_iff_generated (by decide) (by decide)).mpr
        ((hd.recognizes_iff (by decide) (by decide)).mp ha)

theorem empty_completionCodes_perm (n : Nat) :
    (completionCodes [] n).Perm (acceptedCodes 3 3 n) := by
  apply (List.perm_ext_iff_of_nodup (completionCodes_nodup [] n)
    (acceptedCodes_nodup 3 3 n)).mpr
  intro code
  exact (mem_completionCodes [] n code).trans (empty_codeCompletion_iff n code)

/-- The initial completion sequence is the actual unbounded (3,3) distinct
permutation count for every size, not just a finite coefficient prefix. -/
theorem completionCount_empty (n : Nat) :
    completionCount [] n = threeThreeCounts n := by
  rw [completionCount_eq_codes, threeThreeCounts_eq_acceptedCodes]
  exact (empty_completionCodes_perm n).length_eq

#print axioms empty_codeCompletion_iff
#print axioms completionCount_empty
end StackSorting.Generalized.Decorated
