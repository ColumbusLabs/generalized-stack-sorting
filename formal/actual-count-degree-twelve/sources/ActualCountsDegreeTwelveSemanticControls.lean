import ActualCountsDegreeTwelve

/-! Positive semantic boundary checks: the coefficients enumerate distinct
physical outputs or raw one-based sortable inputs, include the empty object
once, and preserve the explicitly proved inverse orientation. -/
noncomputable section
namespace StackSorting.MathlibSeriesBridge
open scoped RatFunc
open StackSorting.Generalized
open ActualCounting

example (n : Nat) : PowerSeries.coeff n generatedCountsPowerSeries =
    ((generatedOutputs 3 3 n).length : ℚ) := by
  rw [generatedCountsPowerSeries_coeff]
  rfl

example (n : Nat) : PowerSeries.coeff n sortableCountsPowerSeries =
    ((oneBasedSortableInputs 3 3 n).length : ℚ) := by
  rw [sortableCountsPowerSeries_coeff]
  rfl

example (n : Nat) : (generatedOutputs 3 3 n).Nodup := generatedOutputs_nodup 3 3 n

example (n : Nat) : (oneBasedSortableInputs 3 3 n).Nodup :=
  oneBasedSortableInputs_nodup (by decide) (by decide) n

example (n : Nat) (output : List Nat) :
    output ∈ generatedOutputs 3 3 n ↔
      Run 3 3 [] (List.range n) output [] :=
  mem_generatedOutputs_iff (by decide) (by decide) output

example (n : Nat) (input : List Nat) :
    input ∈ oneBasedSortableInputs 3 3 n ↔
      input.Perm (List.range' 1 n) ∧ CanSort 3 3 input :=
  mem_oneBasedSortableInputs_iff (by decide) (by decide) input

example (n : Nat) : sortableInputs 3 3 n =
    (generatedOutputs 3 3 n).map inversePermutation := rfl

example : PowerSeries.coeff 0 generatedCountsPowerSeries = 1 :=
  generatedCountsPowerSeries_constantCoeff

example : PowerSeries.coeff 0 sortableCountsPowerSeries = 1 :=
  sortableCountsPowerSeries_constantCoeff

example : (minpoly (RatFunc ℚ) generatedCountsLaurent).natDegree = 12 :=
  generatedCounts_minpoly_degree

example : (minpoly (RatFunc ℚ) sortableCountsLaurent).natDegree = 12 :=
  sortableCounts_minpoly_degree

#check generatedCounts_minpoly_degree
#check sortableCounts_minpoly_degree
#check generatedCounts_annihilator_degree
#check sortableCounts_annihilator_degree
#print axioms generatedCountsLaurent_eq_literal_branch
#print axioms sortableCountsLaurent_eq_literal_branch
#print axioms generatedCounts_minpoly_degree
#print axioms sortableCounts_minpoly_degree
end StackSorting.MathlibSeriesBridge
