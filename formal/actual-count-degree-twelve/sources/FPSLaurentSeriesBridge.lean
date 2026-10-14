import FPSPowerSeriesBridge
import Mathlib.RingTheory.LaurentSeries

/-! Faithful extension of the coefficient-preserving embedding to Laurent
series, together with compatibility with the canonical ℚ(x)-algebra. -/
noncomputable section
namespace StackSorting.MathlibSeriesBridge
open scoped RatFunc
open StackSorting.ProperSeries StackSorting.CauchyRing
open Polynomial

/-- The canonical injective embedding, with no shift or coefficient rescaling. -/
def powerToLaurent : PowerSeries ℚ →+* LaurentSeries ℚ :=
  HahnSeries.ofPowerSeries ℤ ℚ

def toLaurentSeries (a : FPS) : LaurentSeries ℚ := powerToLaurent (toPowerSeries a)

@[simp] theorem coeff_toLaurentSeries (a : FPS) (n : ℕ) :
    (toLaurentSeries a).coeff n = a n := by
  change ((toPowerSeries a : PowerSeries ℚ) : LaurentSeries ℚ).coeff n = a n
  rw [LaurentSeries.coeff_coe_powerSeries, coeff_toPowerSeries]

theorem toLaurentSeries_injective : Function.Injective toLaurentSeries := by
  intro a b h
  apply FPS.ext
  funext n
  have hn := congrArg (fun f : LaurentSeries ℚ => f.coeff n) h
  simpa only [coeff_toLaurentSeries] using hn

theorem toLaurentSeries_coeff_neg (a : FPS) (n : ℤ) (hn : n < 0) :
    (toLaurentSeries a).coeff n = 0 := by
  change ((toPowerSeries a : PowerSeries ℚ) : LaurentSeries ℚ).coeff n = 0
  rw [PowerSeries.coeff_coe, ite_eq_left hn]

/-- The coefficient interpretation induced from ℚ(x) agrees exactly with
polynomial evaluation in the embedded formal variable. -/
theorem ratFunc_coefficient_hom_eq :
    (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).comp
        (algebraMap ℚ[X] (RatFunc ℚ)) =
      Polynomial.eval₂RingHom (powerToLaurent.comp PowerSeries.C)
        (powerToLaurent PowerSeries.X) := by
  apply RingHom.ext
  intro p
  change ((p : RatFunc ℚ) : LaurentSeries ℚ) = _
  rw [← RatFunc.coe_coe p]
  change powerToLaurent (p : PowerSeries ℚ) =
    Polynomial.eval₂ (powerToLaurent.comp PowerSeries.C)
      (powerToLaurent PowerSeries.X) p
  rw [← Polynomial.eval₂_C_X_eq_coe]
  exact Polynomial.hom_eval₂ (p := p) (f := PowerSeries.C) (g := powerToLaurent) PowerSeries.X

/-- Every all-coefficient Core expression identity is preserved in Laurent
series, using precisely the same nonnegative coefficients and zero negatives. -/
theorem coefficient_identity_to_laurentSeries {I : Type}
    (e : PolyExpr I ℚ) (a : Family I ℚ)
    (h : e.eval a = fun _ => (0 : ℚ)) :
    mathEval (powerToLaurent.comp PowerSeries.C) e
      (powerToLaurent PowerSeries.X)
      (fun i => powerToLaurent (PowerSeries.mk (a i))) = 0 := by
  have hp := coefficient_identity_to_powerSeries e a h
  have hl := congrArg powerToLaurent hp
  rw [map_mathEval, map_zero] at hl
  exact hl

#print axioms coeff_toLaurentSeries
#print axioms toLaurentSeries_injective
#print axioms toLaurentSeries_coeff_neg
#print axioms ratFunc_coefficient_hom_eq
#print axioms coefficient_identity_to_laurentSeries
end StackSorting.MathlibSeriesBridge
