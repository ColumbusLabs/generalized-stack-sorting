import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Integral

/-!
Explicit event-to-token size descent. No counting or graph/tree correspondence is assumed.
The size variable is the outer variable in `outerNorm` and `outerContract`.
-/
namespace StackSorting.SizeDescent
open Polynomial
open scoped Polynomial.Bivariate RatFunc
noncomputable section

abbrev expandTwo : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := PowerSeries.expand 2 (by decide)

/-- Faithful transport at even indices. -/
@[simp] theorem coeff_expandTwo (f : PowerSeries ℚ) (n : ℕ) :
    (expandTwo f).coeff (2 * n) = f.coeff n := by
  exact PowerSeries.coeff_expand_mul 2 (by decide) f n

/-- Expansion has no odd-indexed coefficients. -/
@[simp] theorem coeff_expandTwo_odd (f : PowerSeries ℚ) (n : ℕ) :
    (expandTwo f).coeff (2 * n + 1) = 0 := by
  apply PowerSeries.coeff_expand_of_not_dvd
  omega

theorem expandTwo_injective : Function.Injective expandTwo := by
  intro f g h
  ext n
  simpa using congrArg (fun s : PowerSeries ℚ => s.coeff (2 * n)) h


/-- Extract token-size coefficients, without asserting a combinatorial counting correspondence. -/
def halveSeries (h : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => h.coeff (2 * n)

@[simp] theorem coeff_halveSeries (h : PowerSeries ℚ) (n : ℕ) :
    (halveSeries h).coeff n = h.coeff (2 * n) := by
  simp [halveSeries]

@[simp] theorem halveSeries_expandTwo (f : PowerSeries ℚ) : halveSeries (expandTwo f) = f := by
  ext n
  simp

/-- Exact support condition for faithful reconstruction from even coefficients. -/
theorem expandTwo_halveSeries (h : PowerSeries ℚ)
    (hodd : ∀ n, h.coeff (2 * n + 1) = 0) : expandTwo (halveSeries h) = h := by
  ext n
  have hdiv := Nat.mod_add_div n 2
  have hlt := Nat.mod_lt n (by decide : 0 < 2)
  by_cases he : n % 2 = 0
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn, coeff_expandTwo, coeff_halveSeries]
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, coeff_expandTwo_odd, hodd]

/-- Product with the outer-variable sign conjugate. -/
def outerNorm (p : ℚ[X][Y]) : ℚ[X][Y] := p * p.comp (-X)

theorem outerNorm_ne_zero {p : ℚ[X][Y]} (hp : p ≠ 0) : outerNorm p ≠ 0 := by
  exact mul_ne_zero hp (Polynomial.comp_neg_X_eq_zero_iff.not.mpr hp)

theorem outerNorm_invariant (p : ℚ[X][Y]) :
    (outerNorm p).comp (-X) = outerNorm p := by
  simp [outerNorm, mul_comp, comp_neg_X_comp_neg_X, mul_comm]

/-- The norm has zero coefficients at every odd outer exponent. -/
theorem outerNorm_coeff_zero {p : ℚ[X][Y]} {n : ℕ} (hn : ¬2 ∣ n) :
    (outerNorm p).coeff n = 0 := by
  have hodd : Odd n := Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn)
  have hcoeff : ((outerNorm p).comp (-X)).coeff n =
      (outerNorm p).coeff n * (-1 : ℚ[X]) ^ n := by
    have hneg : (C (-1 : ℚ[X]) * X : ℚ[X][Y]) = -X := by
      simp only [map_neg, map_one]
      ring
    rw [← hneg]
    exact Polynomial.comp_C_mul_X_coeff
  rw [outerNorm_invariant, hodd.neg_one_pow, mul_neg_one] at hcoeff
  have htwice : (2 : ℚ[X]) * (outerNorm p).coeff n = 0 := by
    calc
      (2 : ℚ[X]) * (outerNorm p).coeff n = (outerNorm p).coeff n + (outerNorm p).coeff n := by ring
      _ = 0 := eq_neg_iff_add_eq_zero.mp hcoeff
  exact (mul_eq_zero.mp htwice).resolve_left (by norm_num)

/-- Halve the norm's even outer exponents. -/
def outerContract (p : ℚ[X][Y]) : ℚ[X][Y] := Polynomial.contract 2 (outerNorm p)

theorem expand_outerContract (p : ℚ[X][Y]) :
    Polynomial.expand ℚ[X] 2 (outerContract p) = outerNorm p := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_expand (by decide)]
  split_ifs with hn
  · rw [outerContract, Polynomial.coeff_contract (by decide), Nat.div_mul_cancel hn]
  · exact (outerNorm_coeff_zero hn).symm

theorem outerContract_ne_zero {p : ℚ[X][Y]} (hp : p ≠ 0) : outerContract p ≠ 0 := by
  intro h
  have := expand_outerContract p
  rw [h, map_zero] at this
  exact outerNorm_ne_zero hp this.symm

/-- A completely explicit polynomial annihilator transformation, in the usual Q[t][y] order. -/
def descendedPolynomial (p : ℚ[X][Y]) : ℚ[X][Y] :=
  Polynomial.Bivariate.swap (outerContract (Polynomial.Bivariate.swap p))

theorem descendedPolynomial_ne_zero {p : ℚ[X][Y]} (hp : p ≠ 0) :
    descendedPolynomial p ≠ 0 := by
  have hs : Polynomial.Bivariate.swap p ≠ 0 := by
    simpa only [map_zero] using Polynomial.Bivariate.swap.injective.ne hp
  simpa only [descendedPolynomial, map_zero] using
    Polynomial.Bivariate.swap.injective.ne (outerContract_ne_zero hs)

abbrev evaluate (f : PowerSeries ℚ) : ℚ[X][Y] →ₐ[ℚ] PowerSeries ℚ :=
  Polynomial.aevalAeval PowerSeries.X f

theorem expand_aevalAeval (f : PowerSeries ℚ) (p : ℚ[X][Y]) :
    expandTwo (Polynomial.aevalAeval f PowerSeries.X p) =
      Polynomial.aevalAeval (expandTwo f) (PowerSeries.X ^ 2) p := by
  have h : expandTwo.comp (Polynomial.aevalAeval f PowerSeries.X) =
      Polynomial.aevalAeval (expandTwo f) (PowerSeries.X ^ 2) := by
    ext n <;> simp
  exact DFunLike.congr_fun h p

theorem aevalAeval_expand (f : PowerSeries ℚ) (p : ℚ[X][Y]) :
    Polynomial.aevalAeval f PowerSeries.X (Polynomial.expand ℚ[X] 2 p) =
      Polynomial.aevalAeval f (PowerSeries.X ^ 2) p := by
  induction p using Polynomial.induction_on' with
  | add p q _hp _hq => simp
  | monomial n a => simp [← C_mul_X_pow_eq_monomial]

/-- The explicit contracted norm annihilates the unexpanded series. -/
theorem descendedPolynomial_annihilates (f : PowerSeries ℚ) (p : ℚ[X][Y])
    (hp : evaluate (expandTwo f) p = 0) :
    evaluate f (descendedPolynomial p) = 0 := by
  apply expandTwo_injective
  rw [map_zero]
  change expandTwo (Polynomial.aevalAeval PowerSeries.X f
    (Polynomial.Bivariate.swap (outerContract (Polynomial.Bivariate.swap p)))) = 0
  rw [Polynomial.Bivariate.aevalAeval_swap, expand_aevalAeval, ← aevalAeval_expand,
    expand_outerContract]
  simp only [outerNorm, map_mul]
  rw [Polynomial.Bivariate.aevalAeval_swap]
  change evaluate (expandTwo f) p * _ = 0
  rw [hp, zero_mul]

abbrev includeSeries : PowerSeries ℚ →+* LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ

/-- The bivariate evaluation agrees faithfully with the standard Laurent-series interpretation. -/
theorem include_evaluate (f : PowerSeries ℚ) (p : ℚ[X][Y]) :
    includeSeries (evaluate f p) = Polynomial.aeval (R := ℚ[X]) (includeSeries f) p := by
  have h : includeSeries.comp (evaluate f).toRingHom =
      (Polynomial.aeval (R := ℚ[X]) (includeSeries f)).toRingHom := by
    ext n m <;> simp [evaluate, includeSeries, Polynomial.aevalAeval]
  exact DFunLike.congr_fun h p

theorem algebraic_iff_annihilator (f : PowerSeries ℚ) :
    IsAlgebraic (RatFunc ℚ) (includeSeries f) ↔
      ∃ p : ℚ[X][Y], p ≠ 0 ∧ evaluate f p = 0 := by
  rw [← IsFractionRing.isAlgebraic_iff ℚ[X] (RatFunc ℚ) (LaurentSeries ℚ)]
  constructor
  · rintro ⟨p, hp, heval⟩
    refine ⟨p, hp, HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ) ?_⟩
    rw [map_zero, include_evaluate]
    exact heval
  · rintro ⟨p, hp, heval⟩
    refine ⟨p, hp, ?_⟩
    rw [← include_evaluate, heval, map_zero]

/-- Algebraicity descends from event size 2n to token size n. -/
theorem algebraic_of_expandTwo (f : PowerSeries ℚ)
    (h : IsAlgebraic (RatFunc ℚ) (includeSeries (expandTwo f))) :
    IsAlgebraic (RatFunc ℚ) (includeSeries f) := by
  obtain ⟨p, hp, heval⟩ := (algebraic_iff_annihilator _).mp h
  exact (algebraic_iff_annihilator _).mpr
    ⟨descendedPolynomial p, descendedPolynomial_ne_zero hp,
      descendedPolynomial_annihilates f p heval⟩

/-- Reconstruction plus algebraicity of the event series implies algebraicity after halving. -/
theorem halveSeries_algebraic (h : PowerSeries ℚ)
    (ha : IsAlgebraic (RatFunc ℚ) (includeSeries h))
    (hodd : ∀ n, h.coeff (2 * n + 1) = 0) :
    IsAlgebraic (RatFunc ℚ) (includeSeries (halveSeries h)) := by
  apply algebraic_of_expandTwo
  rwa [expandTwo_halveSeries h hodd]

/-- The empty object may be added after descending a nonempty-object event series. -/
theorem one_add_halveSeries_algebraic (h : PowerSeries ℚ)
    (ha : IsAlgebraic (RatFunc ℚ) (includeSeries h))
    (hodd : ∀ n, h.coeff (2 * n + 1) = 0) :
    IsAlgebraic (RatFunc ℚ) (includeSeries (1 + halveSeries h)) := by
  rw [map_add, map_one]
  exact isAlgebraic_one.add (halveSeries_algebraic h ha hodd)

#print axioms StackSorting.SizeDescent.algebraic_of_expandTwo
#print axioms StackSorting.SizeDescent.descendedPolynomial_annihilates
end
end StackSorting.SizeDescent
