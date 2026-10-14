import MarginalNestedProjection
import OwnerRelativizeValues

namespace StackSorting.GraphWidth.MarginalA2.NestedSyntax
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership CapturedLinkExtraction
variable {α : Type} {a b colors : Nat}
variable (ats : {r : Nat} → InputAtom r → (Fin r → α) → Prop)

theorem eval_binary_values (A : InputAtom 2) (u v : Fin a)
    (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval ats (binary A u v) env sets ↔ ats A (Fin.cases (env u) (fun _ => env v)) := by
  change ats A (fun i => env (pair u v i)) ↔ _
  have he : (fun i => env (pair u v i))=Fin.cases (env u) (fun _ => env v) := by
    funext i; fin_cases i <;> rfl
  rw [he]

/-- Context extension does not change the represented local relation. -/
theorem eval_earlier_values (u v : Fin a) (env : Fin a → α)
    (sets : Fin (CapturedLinkExtraction.parameterCount colors) → α → Prop) :
    ActualEval ats (earlier colors u v) env sets ↔
      ActualEval ats (earlier colors (0 : Fin 2) 1)
        (Fin.cases (env u) (fun _ => env v)) sets := by
  simp only [earlier,ActualEval,eval_binary_values,unary,Fin.cases_zero,Fin.cases_succ]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply exists_congr
  intro owner
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  rw [eval_project,eval_project]
  apply OwnerMerge.eval_relativize_values
  · rfl
  · intro i
    fin_cases i <;> rfl

#print axioms eval_earlier_values
end StackSorting.GraphWidth.MarginalA2.NestedSyntax
