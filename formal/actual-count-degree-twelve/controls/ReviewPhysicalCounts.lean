import ActualCountsDegreeTwelve
noncomputable section
namespace IndependentCountReview
open scoped RatFunc
open StackSorting.MathlibSeriesBridge
open StackSorting.Generalized StackSorting.Generalized.ActualCounting
open StackSorting.DegreeTwelve

theorem physical_series_exists : ∃ f : LaurentSeries ℚ,
    (∀ n : ℕ, f.coeff n = ((generatedOutputs 3 3 n).length : ℚ)) ∧
    (∀ n : ℤ, n < 0 → f.coeff n = 0) ∧
    Polynomial.aeval f scalarRatFuncPolynomial = 0 ∧
    (minpoly (RatFunc ℚ) f).natDegree = 12 := by
  refine ⟨generatedCountsLaurent, ?_, generatedCountsLaurent_coeff_neg,
    generatedCountsLaurent_root, generatedCounts_minpoly_degree⟩
  intro n
  exact generatedCountsLaurent_coeff n

theorem sortable_series_exists : ∃ f : LaurentSeries ℚ,
    (∀ n : ℕ, f.coeff n = ((oneBasedSortableInputs 3 3 n).length : ℚ)) ∧
    (minpoly (RatFunc ℚ) f).natDegree = 12 := by
  refine ⟨sortableCountsLaurent, ?_, sortableCounts_minpoly_degree⟩
  intro n
  exact sortableCountsLaurent_coeff n

theorem empty_output_witness : ([] : List Nat) ∈ generatedOutputs 3 3 0 := by
  apply (mem_generatedOutputs_iff (by decide) (by decide) []).mpr
  exact Run.nil []

theorem empty_input_witness : ([] : List Nat) ∈ oneBasedSortableInputs 3 3 0 := by
  apply (mem_oneBasedSortableInputs_iff (by decide) (by decide) []).mpr
  constructor
  · exact List.Perm.refl []
  · exact ⟨[], rfl, rfl⟩

theorem singleton_generated_count : threeThreeCounts 1 = 1 := by decide

theorem singleton_sortable_count : threeThreeSortableCounts 1 = 1 := by
  rw [threeThreeSortableCounts_eq]
  exact singleton_generated_count

theorem empty_laurent_coefficient : generatedCountsLaurent.coeff (0 : ℤ) = 1 := by
  simpa [threeThreeCounts_zero] using generatedCountsLaurent_coeff 0

theorem no_negative_coefficient : sortableCountsLaurent.coeff (-1 : ℤ) = 0 :=
  sortableCountsLaurent_coeff_neg _ (by decide)

theorem actual_nonzero : generatedCountsLaurent ≠ 0 := by
  intro h
  have hc := empty_laurent_coefficient
  rw [h] at hc
  simp at hc

theorem zero_annihilates_but_does_not_bound :
    Polynomial.aeval generatedCountsLaurent (0 : Polynomial (RatFunc ℚ)) = 0 ∧
    ¬ 12 ≤ (0 : Polynomial (RatFunc ℚ)).natDegree := by
  constructor
  · exact map_zero _
  · simp

theorem physical_all_size_semantics (n : Nat) (p : List Nat) :
    (p ∈ generatedOutputs 3 3 n ↔ Run 3 3 [] (List.range n) p []) ∧
    (p ∈ oneBasedSortableInputs 3 3 n ↔ p.Perm (List.range' 1 n) ∧ CanSort 3 3 p) :=
  ⟨mem_generatedOutputs_iff (by decide) (by decide) p,
   mem_oneBasedSortableInputs_iff (by decide) (by decide) p⟩

#print axioms physical_series_exists
#print axioms sortable_series_exists
#print axioms empty_output_witness
#print axioms empty_input_witness
#print axioms singleton_generated_count
#print axioms actual_nonzero
#print axioms zero_annihilates_but_does_not_bound
#print axioms physical_all_size_semantics
end IndependentCountReview
