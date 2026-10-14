import ActualNestedSourceWitness
import CanonicalPhysicalAlgebraicity

/-!
Final positive-width exact-counting and algebraicity endpoints, with constructed uniform admissibility.

The original source passed the independent final 607-module review on 2026-10-14.
This publication revision, dated 2026-10-14, changes only this header;
declarations and proofs are unchanged.
Original accepted source SHA-256: 2846d861e6719ef7c59aae24eceed1aaf603afce7b2c246d06be84619d119688
-/
namespace StackSorting.GraphWidth.GeneralConstruction
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseTreeCompiler.CanonicalCounting Nested.IntroductionSyntax
open GeneralAlgebraicity
open scoped RatFunc

noncomputable def stackEarlier (r s : Nat) :=
  nestedEarlier (finalInterpretation (12*max r s)) (finalVertexTag (12*max r s))

noncomputable def stackBagBound (r s : Nat) :=
  (12*max r s+1)+MarginalA2.localColors (12*max r s)

/-- Genuine existence discharges the accepted conditional counting interface;
the empty physical model is handled by the accepted semantic wrapper. -/
theorem stack_uniform_admissibility (r s : Nat) :
    UniformAdmissibility (stackEarlier r s) (stackBagBound r s) r s := by
  exact canonical_nested_witnesses_give_uniform_admissibility
    (finalInterpretation (12*max r s)) (finalVertexTag (12*max r s))
    (12*max r s+1) (MarginalA2.localColors (12*max r s)) r s
    (fun _ _ hp hr he => canonical_nested_witness hp hr he)

/-- Exact coefficient equality for the original positive-width physical
machine. Canonical trees count outputs, without decomposition multiplicity. -/
theorem stack_exact_count {r s : Nat} (hr : 0<r) (hs : 0<s) (n : Nat) :
    (acceptedTrees (stackEarlier r s) (stackBagBound r s) r s (2*n)).card =
      Generalized.ActualCounting.generatedCount r s n :=
  accepted_card_generatedCount (stackEarlier r s) hr hs (stack_uniform_admissibility r s) n

/-- Positive-width actual distinct-output generating series. -/
theorem stack_output_series_algebraic {r s : Nat} (hr : 0<r) (hs : 0<s) :
    IsAlgebraic (RatFunc ℚ) (includePowerSeries ℚ (actualOutputSeries r s)) :=
  actualOutputSeries_algebraic_of_uniform_admissibility
    (stackEarlier r s) hr hs (stack_uniform_admissibility r s)

/-- Positive-width actual sortable-input generating series. -/
theorem stack_sortable_series_algebraic {r s : Nat} (hr : 0<r) (hs : 0<s) :
    IsAlgebraic (RatFunc ℚ) (includePowerSeries ℚ (actualSortableSeries r s)) :=
  actualSortableSeries_algebraic_of_uniform_admissibility
    (stackEarlier r s) hr hs (stack_uniform_admissibility r s)

#print axioms stack_uniform_admissibility
#print axioms stack_exact_count
#print axioms stack_output_series_algebraic
#print axioms stack_sortable_series_algebraic
end StackSorting.GraphWidth.GeneralConstruction
