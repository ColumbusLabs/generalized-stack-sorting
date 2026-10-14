import CanonicalPhysicalCardinality
import FiniteTreeMSOAlgebraicity
import SizeDescent
import GeneralizedSortableCounting

set_option backward.isDefEq.respectTransparency false

namespace StackSorting.SparseTreeCompiler.CanonicalCounting
open TreeAutomaton TreeAutomaton.Logic SparseEndpointMSO
open Generalized Generalized.ActualCounting FinitePort GeneralAlgebraicity
open scoped RatFunc
noncomputable section

local instance {W : Nat} : DecidableEq (Alphabet 2 2 W) := Classical.decEq _

/-- The executable distinct-output series, with original-machine semantics at positive slot widths. -/
def actualOutputSeries (r s : Nat) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (generatedCount r s n : ℚ)

def canonicalLanguage {k : Nat} (earlier : SparseEndpointMSO.Formula 2 k)
    (b r s : Nat) : Set (BinaryTree (Alphabet 2 2 (b-1))) :=
  {t | (canonicalCodeSentence earlier b r s).EvalAt t Fin.elim0}

theorem coeff_canonicalLanguage {k : Nat} (earlier : SparseEndpointMSO.Formula 2 k)
    (b r s m : Nat) :
    (languageSeries (canonicalLanguage earlier b r s)).coeff m =
      ((acceptedTrees earlier b r s m).card : ℚ) := by
  classical
  simp only [languageSeries,PowerSeries.coeff_mk]
  rfl

theorem actualOutputSeries_eq_halve {k b r s : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (hr : 0<r) (hs : 0<s)
    (hU : UniformAdmissibility earlier b r s) :
    actualOutputSeries r s = SizeDescent.halveSeries (languageSeries (canonicalLanguage earlier b r s)) := by
  classical
  apply PowerSeries.ext
  intro n
  rw [SizeDescent.coeff_halveSeries,coeff_canonicalLanguage,
    accepted_card_generatedCount earlier hr hs hU]
  simp [actualOutputSeries]

/-- Exact event-size/token-size correspondence, proved from the finite
physical bijection and odd-size impossibility rather than assumed. -/
theorem canonicalLanguage_eq_expand_actual {k b r s : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (hr : 0<r) (hs : 0<s)
    (hU : UniformAdmissibility earlier b r s) :
    languageSeries (canonicalLanguage earlier b r s) = SizeDescent.expandTwo (actualOutputSeries r s) := by
  classical
  rw [actualOutputSeries_eq_halve earlier hr hs hU]
  symm
  apply SizeDescent.expandTwo_halveSeries
  intro n
  rw [coeff_canonicalLanguage,accepted_card_odd]
  simp

/-- The final counting/algebra join is conditional only on the separately
constructed uniform supported-admissibility theorem. That genuine existence
premise is explicit; it is not supplied by this component. -/
theorem actualOutputSeries_algebraic_of_uniform_admissibility {k b r s : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (hr : 0<r) (hs : 0<s)
    (hU : UniformAdmissibility earlier b r s) :
    IsAlgebraic (RatFunc ℚ) (includePowerSeries ℚ (actualOutputSeries r s)) := by
  classical
  apply SizeDescent.algebraic_of_expandTwo
  rw [← canonicalLanguage_eq_expand_actual earlier hr hs hU]
  exact (canonicalCode_recognizable earlier b r s).languageSeries_algebraic

/-- At positive slot widths, these are the actual raw sortable input counts.
The executable input/output counts agree at the level of their definitions;
the positive-width original-machine interpretation is the
accepted original-machine inverse-permutation correspondence. -/
def actualSortableSeries (r s : Nat) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (sortableCount r s n : ℚ)

theorem actualSortableSeries_eq_output (r s : Nat) :
    actualSortableSeries r s = actualOutputSeries r s := by
  apply PowerSeries.ext
  intro n
  simp [actualSortableSeries,actualOutputSeries,sortableCount_eq_generatedCount]

theorem actualSortableSeries_algebraic_of_uniform_admissibility {k b r s : Nat}
    (earlier : SparseEndpointMSO.Formula 2 k) (hr : 0<r) (hs : 0<s)
    (hU : UniformAdmissibility earlier b r s) :
    IsAlgebraic (RatFunc ℚ) (includePowerSeries ℚ (actualSortableSeries r s)) := by
  rw [actualSortableSeries_eq_output]
  exact actualOutputSeries_algebraic_of_uniform_admissibility earlier hr hs hU

#print axioms canonicalLanguage_eq_expand_actual
#print axioms actualOutputSeries_algebraic_of_uniform_admissibility
#print axioms actualSortableSeries_algebraic_of_uniform_admissibility
end
end StackSorting.SparseTreeCompiler.CanonicalCounting
