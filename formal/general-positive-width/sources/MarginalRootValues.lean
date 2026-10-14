import MarginalEarlierValues

namespace StackSorting.GraphWidth.MarginalA2.NestedSyntax
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy CapturedLinkExtraction
variable {α : Type} {a colors : Nat}

theorem eval_forestRoot_values (ats : {r : Nat} → InputAtom r → (Fin r → α) → Prop)
    (u : Fin a) (env : Fin a → α)
    (sets : Fin (CapturedLinkExtraction.parameterCount colors) → α → Prop) :
    ActualEval ats (forestRoot colors u) env sets ↔
      ActualEval ats (forestRoot colors (0 : Fin 1)) (fun _ => env u) sets := by
  simp only [forestRoot,ActualEval,unary]
  apply and_congr Iff.rfl
  apply not_congr
  apply exists_congr
  intro z
  have hl := eval_earlier_values ats 0 u.succ (Fin.cases z env) sets
  have hr := eval_earlier_values ats (0 : Fin 2) (0 : Fin 1).succ (Fin.cases z (fun _ => env u)) sets
  exact hl.trans hr.symm

#print axioms eval_forestRoot_values
end StackSorting.GraphWidth.MarginalA2.NestedSyntax
