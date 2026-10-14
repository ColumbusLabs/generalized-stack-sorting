import FPSLaurentSeriesBridge
import LiteralBranchDegreeTwelve
import GeneralizedSortableScalarEquation
import DegreeTwelveMinimalRoot

/-! Exact degree twelve over ℚ(x) for the all-length counting series of
both generated outputs and raw sortable inputs of the unrestricted-height
(3,3) generalized stack. The root identity below is proved from the finite
machine certificates and the coefficient-preserving bridge, not assumed. -/
noncomputable section
namespace StackSorting.MathlibSeriesBridge
open scoped RatFunc
open StackSorting.ProperSeries StackSorting.ConcreteScalar
open StackSorting.Generalized
open StackSorting.Generalized.Decorated.SignedCompletion
open StackSorting.DegreeTwelve
open Polynomial

/-- Counts distinct generated permutations, not accepting histories. -/
def generatedCountsPowerSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (ActualCounting.threeThreeCounts n : ℚ))

/-- Counts distinct raw sortable inputs, via the proved inversion bijection. -/
def sortableCountsPowerSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (ActualCounting.threeThreeSortableCounts n : ℚ))

def generatedCountsLaurent : LaurentSeries ℚ := powerToLaurent generatedCountsPowerSeries

def sortableCountsLaurent : LaurentSeries ℚ := powerToLaurent sortableCountsPowerSeries

@[simp] theorem generatedCountsPowerSeries_coeff (n : ℕ) :
    PowerSeries.coeff n generatedCountsPowerSeries =
      (ActualCounting.threeThreeCounts n : ℚ) := PowerSeries.coeff_mk _ _

@[simp] theorem sortableCountsPowerSeries_coeff (n : ℕ) :
    PowerSeries.coeff n sortableCountsPowerSeries =
      (ActualCounting.threeThreeSortableCounts n : ℚ) := PowerSeries.coeff_mk _ _

@[simp] theorem generatedCountsLaurent_coeff (n : ℕ) :
    generatedCountsLaurent.coeff n = (ActualCounting.threeThreeCounts n : ℚ) := by
  change (generatedCountsPowerSeries : LaurentSeries ℚ).coeff n = _
  rw [LaurentSeries.coeff_coe_powerSeries, generatedCountsPowerSeries_coeff]

@[simp] theorem sortableCountsLaurent_coeff (n : ℕ) :
    sortableCountsLaurent.coeff n = (ActualCounting.threeThreeSortableCounts n : ℚ) := by
  change (sortableCountsPowerSeries : LaurentSeries ℚ).coeff n = _
  rw [LaurentSeries.coeff_coe_powerSeries, sortableCountsPowerSeries_coeff]

@[simp] theorem generatedCountsPowerSeries_constantCoeff :
    PowerSeries.coeff 0 generatedCountsPowerSeries = 1 := by
  rw [generatedCountsPowerSeries_coeff, ActualCounting.threeThreeCounts_zero]
  rfl

@[simp] theorem sortableCountsPowerSeries_constantCoeff :
    PowerSeries.coeff 0 sortableCountsPowerSeries = 1 := by
  rw [sortableCountsPowerSeries_coeff, ActualCounting.threeThreeSortableCounts_zero]
  rfl

theorem generatedCountsLaurent_coeff_neg (n : ℤ) (hn : n < 0) :
    generatedCountsLaurent.coeff n = 0 := by
  change (generatedCountsPowerSeries : LaurentSeries ℚ).coeff n = 0
  rw [PowerSeries.coeff_coe, ite_eq_left hn]

theorem sortableCountsLaurent_coeff_neg (n : ℤ) (hn : n < 0) :
    sortableCountsLaurent.coeff n = 0 := by
  change (sortableCountsPowerSeries : LaurentSeries ℚ).coeff n = 0
  rw [PowerSeries.coeff_coe, ite_eq_left hn]

theorem generatedCountsPowerSeries_eq_literal_branch :
    generatedCountsPowerSeries = toPowerSeries G := by
  apply PowerSeries.ext
  intro n
  rw [generatedCountsPowerSeries_coeff, coeff_toPowerSeries, literal_G_counts]

theorem sortableCountsPowerSeries_eq_generated :
    sortableCountsPowerSeries = generatedCountsPowerSeries := by
  apply PowerSeries.ext
  intro n
  rw [sortableCountsPowerSeries_coeff, generatedCountsPowerSeries_coeff,
    ActualCounting.threeThreeSortableCounts_eq]

theorem sortableCountsLaurent_eq_generated :
    sortableCountsLaurent = generatedCountsLaurent :=
  congrArg powerToLaurent sortableCountsPowerSeries_eq_generated

/-- Full-series identification with the concrete branch already proved
minimal; no finite coefficient cutoff is used. -/
theorem generatedCountsLaurent_eq_literal_branch :
    generatedCountsLaurent = literalBranchLaurent :=
  congrArg powerToLaurent generatedCountsPowerSeries_eq_literal_branch

theorem sortableCountsLaurent_eq_literal_branch :
    sortableCountsLaurent = literalBranchLaurent := by
  rw [sortableCountsLaurent_eq_generated, generatedCountsLaurent_eq_literal_branch]

/-- The unchanged literal 69-term identity, in Mathlib's power-series ring. -/
theorem generatedCountsPowerSeries_literalQ :
    mathEval PowerSeries.C literalQ PowerSeries.X
      (fun _ => generatedCountsPowerSeries) = 0 :=
  coefficient_identity_to_powerSeries literalQ _ actual_counts_literalQ

/-- Every coefficient of the actual raw sortable-input series satisfies Q. -/
theorem sortableCountsPowerSeries_literalQ :
    mathEval PowerSeries.C literalQ PowerSeries.X
      (fun _ => sortableCountsPowerSeries) = 0 :=
  coefficient_identity_to_powerSeries literalQ _ sortable_counts_literalQ

/-- The actual all-length generated-permutation series is a root; no root
hypothesis appears in this theorem. -/
theorem generatedCountsLaurent_root :
    Polynomial.aeval generatedCountsLaurent scalarRatFuncPolynomial = 0 := by
  rw [scalarRatFuncPolynomial_aeval_eq_literalQ]
  exact coefficient_identity_to_laurentSeries literalQ _ actual_counts_literalQ

/-- The actual all-length raw sortable-input series is a root. -/
theorem sortableCountsLaurent_root :
    Polynomial.aeval sortableCountsLaurent scalarRatFuncPolynomial = 0 := by
  rw [sortableCountsLaurent_eq_generated]
  exact generatedCountsLaurent_root

theorem generatedCountsLaurent_integral :
    IsIntegral (RatFunc ℚ) generatedCountsLaurent :=
  scalar_root_integral _ generatedCountsLaurent_root

theorem sortableCountsLaurent_integral :
    IsIntegral (RatFunc ℚ) sortableCountsLaurent :=
  scalar_root_integral _ sortableCountsLaurent_root

/-- Exact algebraic degree of the physical machine's generated-output series. -/
theorem generatedCounts_minpoly_degree :
    (minpoly (RatFunc ℚ) generatedCountsLaurent).natDegree = 12 :=
  scalar_root_minpoly_degree _ generatedCountsLaurent_root

/-- Exact algebraic degree of the original raw sortable-input series. -/
theorem sortableCounts_minpoly_degree :
    (minpoly (RatFunc ℚ) sortableCountsLaurent).natDegree = 12 :=
  scalar_root_minpoly_degree _ sortableCountsLaurent_root

theorem generatedCounts_annihilator_degree
    (q : (RatFunc ℚ)[X]) (hq : q ≠ 0)
    (hqa : Polynomial.aeval generatedCountsLaurent q = 0) :
    12 ≤ q.natDegree :=
  scalar_root_annihilator_degree _ generatedCountsLaurent_root q hq hqa

theorem sortableCounts_annihilator_degree
    (q : (RatFunc ℚ)[X]) (hq : q ≠ 0)
    (hqa : Polynomial.aeval sortableCountsLaurent q = 0) :
    12 ≤ q.natDegree :=
  scalar_root_annihilator_degree _ sortableCountsLaurent_root q hq hqa

#print axioms generatedCountsPowerSeries_constantCoeff
#print axioms sortableCountsPowerSeries_constantCoeff
#print axioms generatedCountsPowerSeries_eq_literal_branch
#print axioms generatedCountsLaurent_eq_literal_branch
#print axioms sortableCountsLaurent_eq_literal_branch
#print axioms generatedCountsPowerSeries_literalQ
#print axioms sortableCountsPowerSeries_literalQ
#print axioms scalarRatFuncPolynomial_aeval_eq_literalQ
#print axioms generatedCountsLaurent_root
#print axioms sortableCountsLaurent_root
#print axioms generatedCountsLaurent_integral
#print axioms sortableCountsLaurent_integral
#print axioms generatedCounts_minpoly_degree
#print axioms sortableCounts_minpoly_degree
#print axioms generatedCounts_annihilator_degree
#print axioms sortableCounts_annihilator_degree
end StackSorting.MathlibSeriesBridge
