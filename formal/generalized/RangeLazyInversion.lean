import GeneralizedRangeLazy
namespace StackSorting.Generalized

theorem RangeLazyRun.cons_cases {r s limit next a : Nat} {held out : List Nat}
    (h : RangeLazyRun r s limit next held (a :: out)) :
    (∃ after, Step r s held [] [a] after ∧ RangeLazyRun r s limit next after out) ∨
    (∃ before after, next ≤ a ∧ a < limit ∧ a ∉ held ∧
      Run r s held (List.range' next (a+1-next)) [] before ∧
      Step r s before [] [a] after ∧ RangeLazyRun r s limit (a+1) after out) := by
  cases h with
  | held pop tail => exact Or.inl ⟨_, pop, tail⟩
  | record lower upper fresh read pop tail =>
    exact Or.inr ⟨_, _, lower, upper, fresh, read, pop, tail⟩

end StackSorting.Generalized
