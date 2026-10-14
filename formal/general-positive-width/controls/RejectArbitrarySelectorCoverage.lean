import MarginalMalformedSelectionControl
namespace StackSorting.GraphWidth.MarginalA2.SelectionControls
open FinitePort Nested
/-- EXPECTED FAILURE: replacing the explicitly constructed selection by an
arbitrary empty tuple cannot inherit constructed coverage. -/
theorem false_arbitrary_selector_coverage
    {n t W : Nat} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (C : AdhesionColoring D W) (e : ExtraEdge D) :
    ∃ q : Candidate t W, False ∧ CoversPair D C q e.val.1 e.val.2 := by
  exact selected_coverage D C (chosen_pair D C e)
end StackSorting.GraphWidth.MarginalA2.SelectionControls
