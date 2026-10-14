import FinalStackConstructionControls
open StackSorting.GraphWidth.GeneralConstruction
open StackSorting.SparseTreeCompiler.CanonicalCounting
example : (acceptedTrees (stackEarlier 1 1) (stackBagBound 1 1) 1 1 6).card=6 := by
  exact StackSorting.GraphWidth.GeneralConstruction.Controls.one_stack_three_tokens
