import FiniteTreeSeries
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Algebraicity of the actual generating function of a deterministic finite
binary-tree automaton, including its possible unique empty tree. -/
namespace StackSorting.TreeAutomaton
open StackSorting.ProperSeries StackSorting.GeneralAlgebraicity
open scoped BigOperators RatFunc
noncomputable section
variable {α Q : Type} [Fintype α] [DecidableEq α] [Fintype Q] [DecidableEq Q]

theorem included_constant_integral (c : ℚ) :
    IsIntegral (RatFunc ℚ) (includePowerSeries ℚ (PowerSeries.C c)) := by
  have h : includePowerSeries ℚ (PowerSeries.C c) =
      algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
        (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c)) := by
    have e := RingHom.congr_fun (coefficient_hom_eq (K := ℚ)) (Polynomial.C c)
    simpa using e.symm
  rw [h]
  exact isIntegral_algebraMap

theorem totalSeries_integral (A : Automaton α Q) (q : Q) :
    IsIntegral (RatFunc ℚ) (includePowerSeries ℚ (totalSeries A q)) := by
  rw [totalSeries_eq, map_add]
  exact (included_constant_integral _).add (positiveSeries_integral A q)

/-- A coefficient is the finite cardinality of distinct accepted trees. -/
def acceptedSeries (A : Automaton α Q) (accept : Finset Q) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((acceptedTrees A accept n).card : ℚ)

omit [Fintype Q] in
@[simp] theorem coeff_acceptedSeries (A : Automaton α Q) (accept : Finset Q) (n : ℕ) :
    PowerSeries.coeff n (acceptedSeries A accept) = ((acceptedTrees A accept n).card : ℚ) := by
  simp [acceptedSeries]

omit [Fintype Q] in
theorem acceptedSeries_eq_sum (A : Automaton α Q) (accept : Finset Q) :
    acceptedSeries A accept = ∑ q ∈ accept, totalSeries A q := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_acceptedSeries, map_sum, coeff_totalSeries, acceptedTrees_card]
  push_cast
  rfl

/-- No recurrence, root, algebraicity or unambiguity hypothesis is supplied:
deterministic evaluation and the tree root bijection derive them. -/
theorem acceptedSeries_integral (A : Automaton α Q) (accept : Finset Q) :
    IsIntegral (RatFunc ℚ) (includePowerSeries ℚ (acceptedSeries A accept)) := by
  rw [acceptedSeries_eq_sum, map_sum]
  exact IsIntegral.sum _ fun q _ => totalSeries_integral A q

theorem acceptedSeries_algebraic (A : Automaton α Q) (accept : Finset Q) :
    IsAlgebraic (RatFunc ℚ) (includePowerSeries ℚ (acceptedSeries A accept)) :=
  (acceptedSeries_integral A accept).isAlgebraic

#print axioms totalSeries_integral
#print axioms coeff_acceptedSeries
#print axioms acceptedSeries_eq_sum
#print axioms acceptedSeries_integral
#print axioms acceptedSeries_algebraic
end
end StackSorting.TreeAutomaton
