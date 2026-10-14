import DegreeTwelveRationalIrreducible
import Mathlib.FieldTheory.Minpoly.Field

/-! Exact degree for any root of the certified scalar polynomial. Applying
this to the machine-counting series still requires its semantic embedding. -/
namespace StackSorting.DegreeTwelve
open Polynomial
noncomputable section

def scalarRatFuncPolynomial : (RatFunc ℚ)[X] :=
  scalarPolynomial.map (algebraMap ℚ[X] (RatFunc ℚ))

theorem scalarRatFuncPolynomial_irreducible : Irreducible scalarRatFuncPolynomial :=
  scalarPolynomial_ratFunc_irreducible

theorem scalarRatFuncPolynomial_degree : scalarRatFuncPolynomial.natDegree = 12 := by
  rw [scalarRatFuncPolynomial,
    natDegree_map_eq_of_injective (IsFractionRing.injective ℚ[X] (RatFunc ℚ))]
  exact scalarPolynomial_degree

theorem scalar_root_integral {A : Type*} [Ring A] [Algebra (RatFunc ℚ) A]
    (a : A) (hroot : aeval a scalarRatFuncPolynomial = 0) :
    IsIntegral (RatFunc ℚ) a := by
  refine ⟨scalarRatFuncPolynomial * C scalarRatFuncPolynomial.leadingCoeff⁻¹,
    monic_mul_leadingCoeff_inv scalarRatFuncPolynomial_irreducible.ne_zero, ?_⟩
  change aeval a (scalarRatFuncPolynomial * C scalarRatFuncPolynomial.leadingCoeff⁻¹) = 0
  rw [map_mul, hroot, zero_mul]

theorem scalar_root_minpoly_degree {A : Type*} [Ring A] [Algebra (RatFunc ℚ) A]
    [Nontrivial A] (a : A) (hroot : aeval a scalarRatFuncPolynomial = 0) :
    (minpoly (RatFunc ℚ) a).natDegree = 12 := by
  rw [← minpoly.eq_of_irreducible scalarRatFuncPolynomial_irreducible hroot,
    natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr
      scalarRatFuncPolynomial_irreducible.ne_zero))]
  exact scalarRatFuncPolynomial_degree

theorem scalar_root_annihilator_degree {A : Type*} [Ring A]
    [Algebra (RatFunc ℚ) A] [Nontrivial A]
    (a : A) (hroot : aeval a scalarRatFuncPolynomial = 0)
    (q : (RatFunc ℚ)[X]) (hq : q ≠ 0) (hqa : aeval a q = 0) :
    12 ≤ q.natDegree := by
  rw [← scalarRatFuncPolynomial_degree]
  exact natDegree_le_of_dvd
    ((scalarRatFuncPolynomial_irreducible.dvd_iff_aeval_eq_zero hroot).mp hqa) hq

#print axioms scalarRatFuncPolynomial_degree
#print axioms scalar_root_integral
#print axioms scalar_root_minpoly_degree
#print axioms scalar_root_annihilator_degree
end
end StackSorting.DegreeTwelve
