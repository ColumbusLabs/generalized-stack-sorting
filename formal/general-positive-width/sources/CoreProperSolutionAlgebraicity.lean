import ProperPowerSeriesAlgebraicity
import FPSPowerSeriesBridge

/-! Algebraicity of the project's exact coefficient-recursive proper solution.
The proof preserves every coefficient, reifies the actual expression syntax,
and applies the proved proper power-series system theorem. -/
namespace StackSorting.GeneralAlgebraicity
open StackSorting.ProperSeries StackSorting.SeriesPolynomialSemantics
open StackSorting.MathlibSeriesBridge
open scoped RatFunc
noncomputable section

variable {I : Type}

/-- The same finite arithmetic syntax, over the polynomial coefficient ring. -/
def coreExprPolynomial : PolyExpr I ℚ → MvPolynomial I (Polynomial ℚ)
  | .scalar q => MvPolynomial.C (Polynomial.C q)
  | .x => MvPolynomial.C Polynomial.X
  | .unknown i => MvPolynomial.X i
  | .add a b => coreExprPolynomial a + coreExprPolynomial b
  | .mul a b => coreExprPolynomial a * coreExprPolynomial b
  | .neg a => -coreExprPolynomial a

theorem coreExprPolynomial_eval (e : PolyExpr I ℚ) (a : I → PowerSeries ℚ) :
    MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom a (coreExprPolynomial e) =
      mathEval PowerSeries.C e PowerSeries.X a := by
  induction e with
  | scalar q => simp [coreExprPolynomial, mathEval]
  | x => simp [coreExprPolynomial, mathEval]
  | unknown i => simp [coreExprPolynomial, mathEval]
  | add e f he hf => simp only [coreExprPolynomial, MvPolynomial.eval₂_add, mathEval, he, hf]
  | mul e f he hf => simp only [coreExprPolynomial, MvPolynomial.eval₂_mul, mathEval, he, hf]
  | neg e he => simp only [coreExprPolynomial, MvPolynomial.eval₂_neg, mathEval, he]

/-- This equation is derived from the original recursive coefficient function,
not taken as an additional assumption about an arbitrarily chosen root. -/
theorem coreProperSolution_powerSeries_equation (R : I → PolyExpr I ℚ) (i : I) :
    PowerSeries.mk (properSolution R i) = PowerSeries.X *
      MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
        (fun j => PowerSeries.mk (properSolution R j)) (coreExprPolynomial (R i)) := by
  have h : (⟨properSolution R i⟩ : CauchyRing.FPS) =
      CauchyRing.X * ringEval (R i) CauchyRing.X
        (fun j => ⟨properSolution R j⟩) := by
    apply CauchyRing.FPS.ext
    rw [X_mul_coeff, ringEval_coefficient_semantics]
    exact properSolution_equation R i
  have hp := congrArg toPowerSeries h
  rw [toPowerSeries_mul, toPowerSeries_X, toPowerSeries_ringEval,
    toPowerSeries_X] at hp
  rw [coreExprPolynomial_eval]
  exact hp

/-- For any finite system, its actual recursively generated coefficient
series has a polynomial relation over ℚ(x). -/
theorem coreProperSolution_integral [Fintype I] [DecidableEq I]
    (R : I → PolyExpr I ℚ) (i : I) :
    IsIntegral (RatFunc ℚ)
      (includePowerSeries ℚ (PowerSeries.mk (properSolution R i))) := by
  exact properPowerSeries_integral (fun j => coreExprPolynomial (R j))
    (fun j => PowerSeries.mk (properSolution R j))
    (coreProperSolution_powerSeries_equation R) i

theorem coreProperSolution_algebraic [Fintype I] [DecidableEq I]
    (R : I → PolyExpr I ℚ) (i : I) :
    IsAlgebraic (RatFunc ℚ)
      (includePowerSeries ℚ (PowerSeries.mk (properSolution R i))) :=
  (coreProperSolution_integral R i).isAlgebraic

#print axioms coreExprPolynomial_eval
#print axioms coreProperSolution_powerSeries_equation
#print axioms coreProperSolution_integral
#print axioms coreProperSolution_algebraic
end
end StackSorting.GeneralAlgebraicity
