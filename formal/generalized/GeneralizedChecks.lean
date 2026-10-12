import GeneralizedCompatibility
import GeneralizedRangeLazy

namespace StackSorting.Generalized

-- A zero push width really forbids top insertion.
example : step 0 3 (.push 0 7) [] = none := by decide
-- A push beyond the current stack is forbidden even when the width allows it.
example : step 3 3 (.push 1 7) [] = none := by decide
example : step 3 3 (.push 2 7) [9] = none := by decide
-- End insertion is legal exactly when the indexed slot is available.
example : step 3 3 (.push 2 7) [9, 8] = some ([9, 8, 7], []) := by decide
-- Third-position removal distinguishes pop widths two and three.
example : step 2 2 (.pop 2) [2, 1, 0] = none := by decide
example : step 2 3 (.pop 2) [2, 1, 0] = some ([2, 1], [0]) := by decide

def boundaryTrace : List RawOp :=
  [.push 0 0, .push 0 1, .push 0 2, .pop 2, .pop 1, .pop 0]

theorem boundaryTrace_run : run 2 3 boundaryTrace [] = some ([], [0, 1, 2]) := by decide
example : run 2 2 boundaryTrace [] = none := by decide

theorem boundaryTrace_lazy : RangeLazyRun 2 3 3 0 [] [0, 1, 2] := by
  have hr := run_relational 2 3 boundaryTrace [] [] [0, 1, 2] boundaryTrace_run
  have hi : inputs boundaryTrace = List.range 3 := by decide
  rw [hi] at hr
  exact generated_rangeLazy hr

#print axioms boundaryTrace_run
#print axioms boundaryTrace_lazy
end StackSorting.Generalized
