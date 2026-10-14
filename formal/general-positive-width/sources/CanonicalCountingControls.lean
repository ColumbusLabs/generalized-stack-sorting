import CanonicalPhysicalAlgebraicity

namespace StackSorting.SparseTreeCompiler.CanonicalCounting.Controls
open Generalized.ActualCounting

theorem actual_empty_count (r s : Nat) : generatedCount r s 0=1 := by rfl

theorem actual_one_token : generatedCount 1 1 1=1 := by decide

theorem actual_two_tokens : generatedCount 1 1 2=2 := by decide

theorem actual_three_one_stack : generatedCount 1 1 3=5 := by decide

theorem actual_three_three_slots : generatedCount 3 3 3=6 := by decide

theorem actual_empty_coefficient (r s : Nat) : (actualOutputSeries r s).coeff 0=1 := by
  simp [actualOutputSeries,actual_empty_count]

theorem actual_raw_empty_coefficient (r s : Nat) : (actualSortableSeries r s).coeff 0=1 := by
  rw [actualSortableSeries_eq_output,actual_empty_coefficient]

#print axioms actual_empty_count
#print axioms actual_one_token
#print axioms actual_two_tokens
#print axioms actual_three_one_stack
#print axioms actual_three_three_slots
#print axioms actual_empty_coefficient
#print axioms actual_raw_empty_coefficient
end StackSorting.SparseTreeCompiler.CanonicalCounting.Controls
