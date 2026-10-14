import Mathlib.Data.List.Induction
import Mathlib.Tactic

namespace StackSorting.Simon
variable {A : Type*}

def adjacentPairs : List A → List (A × A)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a,b) :: adjacentPairs rest

def oddLast : List A → Option A
  | [] => none
  | [a] => some a
  | _ :: _ :: rest => oddLast rest

theorem adjacentPairs_reconstruct (w : List A) :
    (adjacentPairs w).flatMap (fun z => [z.1,z.2]) ++ (oddLast w).toList = w := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b rest ih _ => simpa [adjacentPairs, oddLast] using congrArg (List.cons a ∘ List.cons b) ih

theorem adjacentPairs_ne_nil (w : List A) (hw : 2 ≤ w.length) :
    adjacentPairs w ≠ [] := by
  cases w with
  | nil => simp at hw
  | cons a w =>
    cases w with
    | nil => simp at hw
    | cons b rest => simp [adjacentPairs]
end StackSorting.Simon
