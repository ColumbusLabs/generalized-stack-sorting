import CoreProperSolutionAlgebraicity

/-! Uniqueness transfer for the exact original properSolution coefficients.
This helper converts a proved power-series equation into that fixed recursion. -/
namespace StackSorting.GeneralAlgebraicity
open StackSorting.ProperSeries StackSorting.SeriesPolynomialSemantics
open StackSorting.MathlibSeriesBridge
noncomputable section
variable {I : Type}

def coreOfPowerSeries (a : PowerSeries ℚ) : CauchyRing.FPS :=
  ⟨fun n => PowerSeries.coeff n a⟩

@[simp] theorem toPowerSeries_coreOfPowerSeries (a : PowerSeries ℚ) :
    toPowerSeries (coreOfPowerSeries a) = a := by
  apply PowerSeries.ext
  intro n
  rw [coeff_toPowerSeries]
  rfl

/-- No new solution is selected: the input equation forces the original
coefficient-recursive function at every degree. -/
theorem powerSeries_eq_coreProperSolution (R : I → PolyExpr I ℚ)
    (a : I → PowerSeries ℚ)
    (ha : ∀ i, a i = PowerSeries.X *
      MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom a
        (coreExprPolynomial (R i))) (i : I) :
    a i = PowerSeries.mk (properSolution R i) := by
  let b : Family I ℚ := fun j n => PowerSeries.coeff n (a j)
  have he : ∀ j, b j = shift ((R j).eval b) := by
    intro j
    have h : coreOfPowerSeries (a j) = CauchyRing.X *
        ringEval (R j) CauchyRing.X (fun k => coreOfPowerSeries (a k)) := by
      apply toPowerSeries_injective
      rw [toPowerSeries_mul, toPowerSeries_X, toPowerSeries_ringEval,
        toPowerSeries_X]
      simp only [toPowerSeries_coreOfPowerSeries]
      rw [← coreExprPolynomial_eval]
      exact ha j
    have hc := congrArg CauchyRing.FPS.coeff h
    rw [X_mul_coeff, ringEval_coefficient_semantics] at hc
    exact hc
  have hb : b = properSolution R := by
    apply fixed_unique (properStep_contracting R)
    · funext j
      exact (he j).symm
    · exact solution_fixed (properStep_contracting R) (fun _ _ => 0)
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk]
  exact congrFun (congrFun hb i) n

#print axioms toPowerSeries_coreOfPowerSeries
#print axioms powerSeries_eq_coreProperSolution
end
end StackSorting.GeneralAlgebraicity
