import Std

/-!
# Single-token generalized stack semantics and deletion projection

A fresh parameterized semantics. Top-first stacks are split at a zero-based
slot; the prefix-length condition is precisely the push or pop width bound.
This file proves arbitrary token filtering, not the composition-state theorem.
-/
namespace StackSorting.Generalized

variable {α : Type}

inductive Step (r s : Nat) : List α → List α → List α → List α → Prop where
  | push (pre post : List α) (x : α) (allowed : pre.length < r) :
      Step r s (pre ++ post) [x] [] (pre ++ x :: post)
  | pop (pre post : List α) (x : α) (allowed : pre.length < s) :
      Step r s (pre ++ x :: post) [] [x] (pre ++ post)

/-- Run records exact input/output words and initial/final physical stacks. -/
inductive Run (r s : Nat) : List α → List α → List α → List α → Prop where
  | nil (held : List α) : Run r s held [] [] held
  | cons {held middle final input output inputs outputs : List α}
      (head : Step r s held input output middle)
      (tail : Run r s middle inputs outputs final) :
      Run r s held (input ++ inputs) (output ++ outputs) final

theorem Run.single {r s : Nat} {held input output final : List α}
    (h : Step r s held input output final) : Run r s held input output final := by
  simpa using Run.cons h (Run.nil final)

theorem Run.append {r s : Nat} {held middle final ins outs ins' outs' : List α}
    (h : Run r s held ins outs middle) (h' : Run r s middle ins' outs' final) :
    Run r s held (ins ++ ins') (outs ++ outs') final := by
  induction h with
  | nil => simpa using h'
  | cons head tail ih => simpa [List.append_assoc] using Run.cons head (ih h')

/-- Erasing any chosen collection of tokens only lowers operation positions.
A surviving operation is still legal; an erased one becomes an empty run. -/
theorem Step.filter {r s : Nat} {held input output final : List α}
    (h : Step r s held input output final) (keep : α → Bool) :
    Run r s (held.filter keep) (input.filter keep) (output.filter keep)
      (final.filter keep) := by
  cases h with
  | push pre post x allowed =>
    have bound : (pre.filter keep).length < r :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) allowed
    cases hx : keep x with
    | false => simpa [List.filter_append, hx] using Run.nil ((pre ++ post).filter keep)
    | true =>
      simpa [List.filter_append, hx] using
        Run.single (Step.push (pre.filter keep) (post.filter keep) x bound)
  | pop pre post x allowed =>
    have bound : (pre.filter keep).length < s :=
      Nat.lt_of_le_of_lt (List.length_filter_le _ _) allowed
    cases hx : keep x with
    | false => simpa [List.filter_append, hx] using Run.nil ((pre ++ post).filter keep)
    | true =>
      simpa [List.filter_append, hx] using
        Run.single (Step.pop (pre.filter keep) (post.filter keep) x bound)

/-- Exact whole-history deletion, with no distinctness or ordering assumptions. -/
theorem Run.filter {r s : Nat} {held input output final : List α}
    (h : Run r s held input output final) (keep : α → Bool) :
    Run r s (held.filter keep) (input.filter keep) (output.filter keep)
      (final.filter keep) := by
  induction h with
  | nil => simpa using Run.nil (List.filter keep _)
  | cons head tail ih =>
      simpa only [List.filter_append] using (head.filter keep).append ih

/-- Generalized stacks are symbol-oblivious: arbitrary relabelling commutes
with every legal history. Injectivity is only needed to identify permutations. -/
theorem Step.map {β : Type} {r s : Nat} {held input output final : List α}
    (h : Step r s held input output final) (f : α → β) :
    Step r s (held.map f) (input.map f) (output.map f) (final.map f) := by
  cases h with
  | push pre post x allowed =>
      simpa using Step.push (pre.map f) (post.map f) (f x) (by simpa using allowed)
  | pop pre post x allowed =>
      simpa using Step.pop (pre.map f) (post.map f) (f x) (by simpa using allowed)

theorem Run.map {β : Type} {r s : Nat} {held input output final : List α}
    (h : Run r s held input output final) (f : α → β) :
    Run r s (held.map f) (input.map f) (output.map f) (final.map f) := by
  induction h with
  | nil => simpa using Run.nil (List.map f _)
  | cons head tail ih => simpa using Run.cons (head.map f) ih

#print axioms Step.filter
#print axioms Run.filter
#print axioms Step.map
#print axioms Run.map
end StackSorting.Generalized
