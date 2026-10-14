import FinitePolynomialSystemAlgebraicity
import Mathlib.RingTheory.LaurentSeries

/-!
The components of a finite proper polynomial system A_i = X * P_i(X,A) are algebraic over the rational-function field.

The original source passed the independent final 607-module review on 2026-10-14.
This publication revision, dated 2026-10-14, changes only this header;
declarations and proofs are unchanged.
Original accepted source SHA-256: 690e917738e1776bbceabebfd4ed896cc8b115278f1f62bbdf2aa3c2e6c44ed2
-/
namespace StackSorting.GeneralAlgebraicity
open MvPolynomial
open scoped RatFunc
noncomputable section

variable (K : Type*) [Field K]

def includePowerSeries : PowerSeries K →+* LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K

@[simp] theorem includePowerSeries_X :
    includePowerSeries K PowerSeries.X = HahnSeries.single 1 1 := by
  exact HahnSeries.ofPowerSeries_X

theorem coefficient_hom_eq :
    (algebraMap (RatFunc K) (LaurentSeries K)).comp
        (algebraMap (Polynomial K) (RatFunc K)) =
      (includePowerSeries K).comp Polynomial.coeToPowerSeries.ringHom := by
  apply RingHom.ext
  intro p
  change ((p : RatFunc K) : LaurentSeries K) = ((p : PowerSeries K) : LaurentSeries K)
  exact (RatFunc.coe_coe p).symm

theorem included_X :
    algebraMap (RatFunc K) (LaurentSeries K)
        (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
      includePowerSeries K PowerSeries.X := by
  simp

variable {K} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A proper system is represented literally over K(x), with its X factor retained. -/
def properRelations (p : ι → MvPolynomial ι (Polynomial K)) (i : ι) :
    MvPolynomial ι (RatFunc K) :=
  X i - C (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) *
    MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) (p i)

omit [Fintype ι] [DecidableEq ι] in
theorem included_polynomial_eval (p : MvPolynomial ι (Polynomial K))
    (a : ι → PowerSeries K) :
    MvPolynomial.aeval (fun i => includePowerSeries K (a i))
        (MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) p) =
      includePowerSeries K (MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom a p) := by
  change MvPolynomial.eval₂ (algebraMap (RatFunc K) (LaurentSeries K))
      (fun i => includePowerSeries K (a i))
      (MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K)) p) = _
  rw [MvPolynomial.eval₂_map, coefficient_hom_eq, ← MvPolynomial.hom_eval₂]

def properJacobianSeries (p : ι → MvPolynomial ι (Polynomial K))
    (a : ι → PowerSeries K) : Matrix ι ι (PowerSeries K) :=
  fun i j => (if i=j then 1 else 0) - PowerSeries.X *
    MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom a (MvPolynomial.pderiv i (p j))

theorem properJacobianSeries_constant (p : ι → MvPolynomial ι (Polynomial K))
    (a : ι → PowerSeries K) :
    PowerSeries.constantCoeff (properJacobianSeries p a).det = 1 := by
  rw [RingHom.map_det]
  have h : (PowerSeries.constantCoeff.mapMatrix (properJacobianSeries p a)) =
      (1 : Matrix ι ι K) := by
    ext i j
    simp [properJacobianSeries, Matrix.one_apply]
  rw [h, Matrix.det_one]

theorem properJacobianSeries_isUnit (p : ι → MvPolynomial ι (Polynomial K))
    (a : ι → PowerSeries K) : IsUnit (properJacobianSeries p a).det := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [properJacobianSeries_constant]
  exact isUnit_one

omit [Fintype ι] in
theorem properRelations_derivative (p : ι → MvPolynomial ι (Polynomial K))
    (a : ι → PowerSeries K) (i j : ι) :
    MvPolynomial.aeval (fun k => includePowerSeries K (a k))
        (MvPolynomial.pderiv i (properRelations p j)) =
      includePowerSeries K (properJacobianSeries p a i j) := by
  by_cases h : i=j
  · subst j
    simp [properRelations, properJacobianSeries, map_sub,
      MvPolynomial.pderiv_map, included_polynomial_eval]
  · simp [properRelations, properJacobianSeries, map_sub,
      MvPolynomial.pderiv_map, included_polynomial_eval, h, Ne.symm h]

theorem properRelations_jacobian (p : ι → MvPolynomial ι (Polynomial K))
    (a : ι → PowerSeries K) :
    MvPolynomial.aeval (fun i => includePowerSeries K (a i))
        (systemJacobian (properRelations p)) =
      includePowerSeries K (properJacobianSeries p a).det := by
  change MvPolynomial.aeval (fun i => includePowerSeries K (a i))
      (Matrix.det (show Matrix ι ι (MvPolynomial ι (RatFunc K)) from
        fun i j => MvPolynomial.pderiv i (properRelations p j))) = _
  rw [AlgHom.map_det, RingHom.map_det]
  congr 1
  ext i j : 1
  exact properRelations_derivative p a i j

/-- Every component of the actual solution of a finite proper polynomial
system is integral over K(x), without a separate nonsingularity hypothesis. -/
theorem properPowerSeries_integral (p : ι → MvPolynomial ι (Polynomial K))
    (a : ι → PowerSeries K)
    (ha : ∀ i, a i = PowerSeries.X *
      MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom a (p i)) (i : ι) :
    IsIntegral (RatFunc K) (includePowerSeries K (a i)) := by
  apply finitePolynomialSystem_integral (properRelations p)
    (fun i => includePowerSeries K (a i))
  · intro j
    simp only [properRelations, map_sub, aeval_X, map_mul, aeval_C,
      included_polynomial_eval, included_X]
    rw [← map_mul, ← ha j, sub_self]
  · rw [properRelations_jacobian]
    exact (properJacobianSeries_isUnit p a).map (includePowerSeries K)

theorem properPowerSeries_algebraic (p : ι → MvPolynomial ι (Polynomial K))
    (a : ι → PowerSeries K)
    (ha : ∀ i, a i = PowerSeries.X *
      MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom a (p i)) (i : ι) :
    IsAlgebraic (RatFunc K) (includePowerSeries K (a i)) :=
  (properPowerSeries_integral p a ha i).isAlgebraic

#print axioms properJacobianSeries_constant
#print axioms properRelations_jacobian
#print axioms properPowerSeries_integral
#print axioms properPowerSeries_algebraic
end
end StackSorting.GeneralAlgebraicity
