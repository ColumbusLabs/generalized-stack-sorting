import ScalarPolynomialMathlibBridge
import FPSLaurentSeriesBridge
import DegreeTwelveMinimalRoot

/-! Exact algebraic degree of the concrete formal branch already constructed
in the Core development. This module does not identify that branch with
physical-machine counts; that final identification is a separate dependency. -/
noncomputable section
namespace StackSorting.MathlibSeriesBridge
open scoped RatFunc
open StackSorting.ConcreteScalar StackSorting.DegreeTwelve
open Polynomial

/-- The existing concrete Core branch, embedded without changing coefficients. -/
def literalBranchLaurent : LaurentSeries ℚ := toLaurentSeries G

/-- The exact polynomial over ℚ(x) evaluates using the canonical inclusion of
its coefficients and the exact unchanged 69-term Core expression. -/
theorem scalarRatFuncPolynomial_aeval_eq_literalQ (g : LaurentSeries ℚ) :
    Polynomial.aeval g scalarRatFuncPolynomial =
      mathEval (powerToLaurent.comp PowerSeries.C) literalQ
        (powerToLaurent PowerSeries.X) (fun _ => g) := by
  rw [aeval_def, scalarRatFuncPolynomial, eval₂_map,
    ratFunc_coefficient_hom_eq, scalarPolynomial_eval₂_eq_literalQ]

/-- The concrete formal branch is a root, using its existing all-coefficient
identity; no root or desired equation is assumed as a theorem hypothesis. -/
theorem literalBranchLaurent_root :
    Polynomial.aeval literalBranchLaurent scalarRatFuncPolynomial = 0 := by
  rw [scalarRatFuncPolynomial_aeval_eq_literalQ]
  exact coefficient_identity_to_laurentSeries literalQ
    (fun _ => G.coeff) literalQ_G_all_coefficients

theorem literalBranchLaurent_integral :
    IsIntegral (RatFunc ℚ) literalBranchLaurent :=
  scalar_root_integral _ literalBranchLaurent_root

theorem literalBranch_minpoly_degree :
    (minpoly (RatFunc ℚ) literalBranchLaurent).natDegree = 12 :=
  scalar_root_minpoly_degree _ literalBranchLaurent_root

theorem literalBranch_annihilator_degree
    (q : (RatFunc ℚ)[X]) (hq : q ≠ 0)
    (hqa : Polynomial.aeval literalBranchLaurent q = 0) :
    12 ≤ q.natDegree :=
  scalar_root_annihilator_degree _ literalBranchLaurent_root q hq hqa

#print axioms scalarRatFuncPolynomial_aeval_eq_literalQ
#print axioms literalBranchLaurent_root
#print axioms literalBranchLaurent_integral
#print axioms literalBranch_minpoly_degree
#print axioms literalBranch_annihilator_degree
end StackSorting.MathlibSeriesBridge
