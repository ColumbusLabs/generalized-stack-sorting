import PositiveWidthStackAlgebraicity
open StackSorting.GraphWidth.GeneralConstruction
open StackSorting.SparseTreeCompiler.CanonicalCounting StackSorting.GeneralAlgebraicity
open scoped RatFunc
example : IsAlgebraic (RatFunc ℚ) (includePowerSeries ℚ (actualOutputSeries 0 1)) := by
  exact stack_output_series_algebraic (r:=0) (s:=1)
