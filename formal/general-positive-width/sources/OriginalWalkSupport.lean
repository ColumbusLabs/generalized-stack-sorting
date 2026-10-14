import HyperpathRouteSplicing

namespace StackSorting.LowPathwidthParts

/-- An actual SimpleGraph walk gives a propositional original-edge walk under
any proved support predicate. -/
theorem original_walk_of_support {V : Type} (G : SimpleGraph V) {P : V → Prop}
    {s t : V} (w : G.Walk s t) (hP : ∀ x ∈ w.support, P x) :
    GraphWidth.Walk G.Adj P s t := by
  induction w with
  | nil => exact .refl (hP _ (by simp))
  | @cons u v w huv tail ih =>
    exact .step (hP u (by simp)) huv (ih (fun x hx => hP x (List.mem_cons_of_mem _ hx)))

end StackSorting.LowPathwidthParts
