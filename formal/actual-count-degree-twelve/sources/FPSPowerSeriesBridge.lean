import SeriesPolynomialSemantics
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Rat.Cast.CharZero

/-! Coefficient-preserving transport from the project's Core/Std Cauchy
formal series to Mathlib's ordinary power-series ring. No algebraic equation
is assumed in constructing this map. -/
noncomputable section
namespace StackSorting.MathlibSeriesBridge
open StackSorting.ProperSeries StackSorting.CauchyRing
open StackSorting.SeriesPolynomialSemantics

/-- The ordinary Mathlib power series having exactly the Core coefficients. -/
def toPowerSeries (a : FPS) : PowerSeries ℚ := PowerSeries.mk a.coeff

@[simp] theorem coeff_toPowerSeries (a : FPS) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeries a) = a n := by
  exact PowerSeries.coeff_mk n a.coeff

theorem toPowerSeries_injective : Function.Injective toPowerSeries := by
  intro a b h
  apply FPS.ext
  funext n
  have hn := congrArg (PowerSeries.coeff n) h
  simpa only [coeff_toPowerSeries] using hn

theorem sumTerms_eq_sum_range (f : ℕ → ℚ) (n : ℕ) :
    sumTerms f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp only [sumTerms, Finset.range_zero, Finset.sum_empty]
  | succ n ih => simp only [sumTerms, Finset.sum_range_succ, ih]

@[simp] theorem toPowerSeries_C (r : ℚ) :
    toPowerSeries (CauchyRing.C r) = PowerSeries.C r := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_toPowerSeries, PowerSeries.coeff_C]
  rfl

@[simp] theorem toPowerSeries_X :
    toPowerSeries CauchyRing.X = PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_toPowerSeries, PowerSeries.coeff_X]
  rfl

@[simp] theorem toPowerSeries_zero : toPowerSeries 0 = 0 := by
  change toPowerSeries (CauchyRing.C 0) = 0
  rw [toPowerSeries_C, map_zero]

@[simp] theorem toPowerSeries_one : toPowerSeries 1 = 1 := by
  change toPowerSeries (CauchyRing.C 1) = 1
  rw [toPowerSeries_C, map_one]

@[simp] theorem toPowerSeries_add (a b : FPS) :
    toPowerSeries (a + b) = toPowerSeries a + toPowerSeries b := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_toPowerSeries, map_add, CauchyRing.add_apply]

@[simp] theorem toPowerSeries_neg (a : FPS) :
    toPowerSeries (-a) = -toPowerSeries a := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_toPowerSeries, map_neg, CauchyRing.neg_apply]

@[simp] theorem toPowerSeries_mul (a b : FPS) :
    toPowerSeries (a * b) = toPowerSeries a * toPowerSeries b := by
  apply PowerSeries.ext
  intro n
  rw [coeff_toPowerSeries, CauchyRing.mul_apply, cauchy,
    sumTerms_eq_sum_range, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_toPowerSeries]

@[simp] theorem toPowerSeries_pow (a : FPS) (n : ℕ) :
    toPowerSeries (a ^ n) = (toPowerSeries a) ^ n := by
  induction n with
  | zero => exact toPowerSeries_one
  | succ n ih =>
    change toPowerSeries (a ^ n * a) = _
    rw [toPowerSeries_mul, ih, pow_succ]

/-- Evaluation of the same Core expression in any commutative ℚ-algebra. -/
def mathEval {I A : Type*} [CommRing A] (c : ℚ →+* A)
    (e : PolyExpr I ℚ) (x : A) (u : I → A) : A :=
  match e with
  | .scalar r => c r
  | .x => x
  | .unknown i => u i
  | .add e f => mathEval c e x u + mathEval c f x u
  | .mul e f => mathEval c e x u * mathEval c f x u
  | .neg e => -mathEval c e x u

/-- The Core ring evaluator transports faithfully, including its Cauchy product. -/
theorem toPowerSeries_ringEval {I : Type} (e : PolyExpr I ℚ)
    (x : FPS) (u : I → FPS) :
    toPowerSeries (ringEval e x u) =
      mathEval PowerSeries.C e (toPowerSeries x) (fun i => toPowerSeries (u i)) := by
  induction e with
  | scalar r => exact toPowerSeries_C r
  | x => rfl
  | unknown i => rfl
  | add e f he hf => simp only [ringEval, mathEval, toPowerSeries_add, he, hf]
  | mul e f he hf => simp only [ringEval, mathEval, toPowerSeries_mul, he, hf]
  | neg e he => simp only [ringEval, mathEval, toPowerSeries_neg, he]

/-- Equality to zero in the original coefficient semantics gives equality to
zero in Mathlib, for the same coefficient sequence at every index. -/
theorem coefficient_identity_to_powerSeries {I : Type} (e : PolyExpr I ℚ)
    (a : Family I ℚ) (h : e.eval a = fun _ => (0 : ℚ)) :
    mathEval PowerSeries.C e PowerSeries.X
      (fun i => PowerSeries.mk (a i)) = 0 := by
  have hr : ringEval e CauchyRing.X (fun i => ⟨a i⟩) = 0 := by
    apply FPS.ext
    rw [ringEval_coefficient_semantics, h]
    funext n
    change 0 = if n = 0 then 0 else 0
    split <;> rfl
  have ht := congrArg toPowerSeries hr
  rw [toPowerSeries_ringEval, toPowerSeries_X, toPowerSeries_zero] at ht
  exact ht

/-- Expression evaluation commutes with every target-ring homomorphism. -/
theorem map_mathEval {I A B : Type*} [CommRing A] [CommRing B]
    (c : ℚ →+* A) (f : A →+* B) (e : PolyExpr I ℚ) (x : A) (u : I → A) :
    f (mathEval c e x u) = mathEval (f.comp c) e (f x) (fun i => f (u i)) := by
  induction e with
  | scalar r => rfl
  | x => rfl
  | unknown i => rfl
  | add e g he hg => simp only [mathEval, map_add, he, hg]
  | mul e g he hg => simp only [mathEval, map_mul, he, hg]
  | neg e he => simp only [mathEval, map_neg, he]

#print axioms toPowerSeries_injective
#print axioms toPowerSeries_mul
#print axioms toPowerSeries_ringEval
#print axioms coefficient_identity_to_powerSeries
#print axioms map_mathEval
end StackSorting.MathlibSeriesBridge
