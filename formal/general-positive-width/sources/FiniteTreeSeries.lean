import FiniteTreeAcceptedLanguage
import CorePowerSeriesUniqueness

/-! Actual deterministic tree counts satisfy a proper polynomial system.
The empty tree is split off explicitly, and every transition consumes one node.
The coefficient recurrence is derived from the two-sided root bijection. -/
namespace StackSorting.TreeAutomaton
open StackSorting.ProperSeries StackSorting.GeneralAlgebraicity
open StackSorting.MathlibSeriesBridge
open scoped BigOperators RatFunc
noncomputable section
variable {α Q : Type} [Fintype α] [DecidableEq α] [DecidableEq Q]

def emptyWeight (A : Automaton α Q) (q : Q) : ℚ :=
  if A.emptyState = q then 1 else 0

def totalSeries (A : Automaton α Q) (q : Q) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (treeCount A q n : ℚ)

def positiveSeries (A : Automaton α Q) (q : Q) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (treeCount A q n : ℚ)

@[simp] theorem coeff_totalSeries (A : Automaton α Q) (q : Q) (n : ℕ) :
    PowerSeries.coeff n (totalSeries A q) = (treeCount A q n : ℚ) := by
  simp [totalSeries]

@[simp] theorem coeff_positiveSeries_zero (A : Automaton α Q) (q : Q) :
    PowerSeries.coeff 0 (positiveSeries A q) = 0 := by
  simp [positiveSeries]

@[simp] theorem coeff_positiveSeries_succ (A : Automaton α Q) (q : Q) (n : ℕ) :
    PowerSeries.coeff (n+1) (positiveSeries A q) = (treeCount A q (n+1) : ℚ) := by
  simp [positiveSeries]

theorem totalSeries_eq (A : Automaton α Q) (q : Q) :
    totalSeries A q = PowerSeries.C (emptyWeight A q) + positiveSeries A q := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [emptyWeight, positiveSeries, apply_ite]
  | succ n => simp

variable [Fintype Q]

/-- This identity counts actual tree objects once, by the root bijection. -/
theorem positiveSeries_equation (A : Automaton α Q) (q : Q) :
    positiveSeries A q = PowerSeries.X *
      ∑ p : Production A q, totalSeries A p.val.2.1 * totalSeries A p.val.2.2 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_positiveSeries_succ, PowerSeries.coeff_succ_X_mul, map_sum]
    simp only [PowerSeries.coeff_mul, coeff_totalSeries]
    rw [treeCount_succ]
    push_cast
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    exact Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal n)
      (fun (ij : ℕ × ℕ) => (treeCount A p.val.2.1 ij.1 : ℚ) * (treeCount A p.val.2.2 ij.2 : ℚ))

/-- Finite sums in the project's original arithmetic syntax. -/
def expressionSum {J : Type} (terms : List (PolyExpr J ℚ)) : PolyExpr J ℚ :=
  terms.foldr PolyExpr.add (.scalar 0)

theorem mathEval_expressionSum {J : Type} (terms : List (PolyExpr J ℚ))
    (a : J → PowerSeries ℚ) :
    mathEval PowerSeries.C (expressionSum terms) PowerSeries.X a =
      (terms.map fun e => mathEval PowerSeries.C e PowerSeries.X a).sum := by
  induction terms with
  | nil => simp [expressionSum, mathEval]
  | cons e es ih =>
    simpa [expressionSum, mathEval] using
      congrArg (fun x => mathEval PowerSeries.C e PowerSeries.X a + x) ih

def childExpression (A : Automaton α Q) (q : Q) : PolyExpr Q ℚ :=
  .add (.scalar (emptyWeight A q)) (.unknown q)

def productionExpression (A : Automaton α Q) (q : Q)
    (p : Production A q) : PolyExpr Q ℚ :=
  .mul (childExpression A p.val.2.1) (childExpression A p.val.2.2)

def treeSystem (A : Automaton α Q) (q : Q) : PolyExpr Q ℚ :=
  expressionSum (Finset.univ.toList.map (productionExpression A q))

theorem treeSystem_eval (A : Automaton α Q) (q : Q) :
    MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom (positiveSeries A)
        (coreExprPolynomial (treeSystem A q)) =
      ∑ p : Production A q, totalSeries A p.val.2.1 * totalSeries A p.val.2.2 := by
  rw [coreExprPolynomial_eval]
  simp only [treeSystem, mathEval_expressionSum, List.map_map]
  rw [Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Function.comp_apply, productionExpression, childExpression, mathEval]
  rw [← totalSeries_eq, ← totalSeries_eq]

theorem treeSystem_equation (A : Automaton α Q) (q : Q) :
    positiveSeries A q = PowerSeries.X *
      MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom (positiveSeries A)
        (coreExprPolynomial (treeSystem A q)) := by
  rw [treeSystem_eval]
  exact positiveSeries_equation A q

/-- Exact coefficient equality with the original proper recursion, with no
assumed counting recurrence or supplied root. -/
theorem positiveSeries_eq_properSolution (A : Automaton α Q) (q : Q) :
    positiveSeries A q = PowerSeries.mk (properSolution (treeSystem A) q) := by
  exact powerSeries_eq_coreProperSolution (treeSystem A) (positiveSeries A)
    (treeSystem_equation A) q

theorem properSolution_eq_treeCount (A : Automaton α Q) (q : Q) (n : ℕ) :
    properSolution (treeSystem A) q (n+1) = (treeCount A q (n+1) : ℚ) := by
  have h := congrArg (PowerSeries.coeff (n+1)) (positiveSeries_eq_properSolution A q)
  simpa only [coeff_positiveSeries_succ, PowerSeries.coeff_mk] using h.symm

theorem positiveSeries_integral (A : Automaton α Q) (q : Q) :
    IsIntegral (RatFunc ℚ) (includePowerSeries ℚ (positiveSeries A q)) := by
  rw [positiveSeries_eq_properSolution]
  exact coreProperSolution_integral (treeSystem A) q

#print axioms positiveSeries_equation
#print axioms treeSystem_equation
#print axioms positiveSeries_eq_properSolution
#print axioms properSolution_eq_treeCount
#print axioms positiveSeries_integral
end
end StackSorting.TreeAutomaton
