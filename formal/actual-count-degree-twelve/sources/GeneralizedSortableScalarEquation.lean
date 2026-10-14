import GeneralizedActualScalarEquation
import GeneralizedSortableCounting

/-!
The displayed scalar relation for actual one-based sortable-input counts. The semantic list and duplicate-freeness are proved in GeneralizedSortableCounting.

The original source passed the independent actual-count degree review on 2026-10-13.
This publication revision, dated 2026-10-14, changes only this header;
declarations and proofs are unchanged.
Original accepted source SHA-256: 5816c4c69f5a376ab5977f9d9756b472728a8f9fd3906fde53bbf3219762038e
-/
noncomputable section
namespace StackSorting.Generalized.Decorated.SignedCompletion
open StackSorting.CauchyRing StackSorting.ConcreteScalar

theorem literal_G_sortable_counts (n : Nat) :
    G n = (ActualCounting.threeThreeSortableCounts n : Rat) := by
  rw [ActualCounting.threeThreeSortableCounts_eq]
  exact literal_G_counts n

theorem sortable_counts_literalQ :
    literalQ.eval (fun _ => fun n => (ActualCounting.threeThreeSortableCounts n : Rat)) =
      (fun _ => (0 : Rat)) := by
  simpa only [ActualCounting.threeThreeSortableCounts_eq] using actual_counts_literalQ

#print axioms literal_G_sortable_counts
#print axioms sortable_counts_literalQ
end StackSorting.Generalized.Decorated.SignedCompletion
