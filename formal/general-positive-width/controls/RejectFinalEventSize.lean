import PositiveWidthStackAlgebraicity
open StackSorting.GraphWidth.GeneralConstruction
open StackSorting.SparseTreeCompiler.CanonicalCounting
example :
    (acceptedTrees (stackEarlier 1 1) (stackBagBound 1 1) 1 1 3).card =
      StackSorting.Generalized.ActualCounting.generatedCount 1 1 3 := by
  exact stack_exact_count (r:=1) (s:=1) (by decide) (by decide) 3
