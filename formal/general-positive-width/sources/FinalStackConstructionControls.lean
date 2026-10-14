import PositiveWidthStackAlgebraicity
import CanonicalCountingControls
import PhysicalCanonicalTransportControls

/-!
Semantic controls for the final constructed-witness endpoint, including the physical empty case.

The original source passed the independent final 607-module review on 2026-10-14.
This publication revision, dated 2026-10-14, changes only this header;
declarations and proofs are unchanged.
Original accepted source SHA-256: 486cdddd9c679d4f037af259dc3ea7caebcb006f81de02f0b5eee79bfd087f50
-/
namespace StackSorting.GraphWidth.GeneralConstruction.Controls
open SparseTreeCompiler.CanonicalCounting

/-- The physical empty case is included without adding a dummy event. -/
theorem empty_tree_coefficient {r s : Nat} (hr : 0<r) (hs : 0<s) :
    (acceptedTrees (stackEarlier r s) (stackBagBound r s) r s 0).card=1 := by
  simpa only [Nat.mul_zero,StackSorting.SparseTreeCompiler.CanonicalCounting.Controls.actual_empty_count] using
    stack_exact_count hr hs 0

/-- Three tokens correspond to six events; exact counting retains the
one-stack obstruction rather than counting all six permutations. -/
theorem one_stack_three_tokens :
    (acceptedTrees (stackEarlier 1 1) (stackBagBound 1 1) 1 1 6).card=5 := by
  have h := stack_exact_count (r:=1) (s:=1) (by decide) (by decide) 3
  simpa only [StackSorting.SparseTreeCompiler.CanonicalCounting.Controls.actual_three_one_stack] using h

/-- A second concrete coefficient distinguishes the wider physical machine. -/
theorem three_slots_three_tokens :
    (acceptedTrees (stackEarlier 3 3) (stackBagBound 3 3) 3 3 6).card=6 := by
  have h := stack_exact_count (r:=3) (s:=3) (by decide) (by decide) 3
  simpa only [StackSorting.SparseTreeCompiler.CanonicalCounting.Controls.actual_three_three_slots] using h

/-- Keep the actual raw sortable-input coefficient, not a tree-size count. -/
theorem empty_sortable_coefficient (r s : Nat) :
    (actualSortableSeries r s).coeff 0=1 :=
  StackSorting.SparseTreeCompiler.CanonicalCounting.Controls.actual_raw_empty_coefficient r s

#print axioms empty_tree_coefficient
#print axioms one_stack_three_tokens
#print axioms three_slots_three_tokens
#print axioms empty_sortable_coefficient
end StackSorting.GraphWidth.GeneralConstruction.Controls
