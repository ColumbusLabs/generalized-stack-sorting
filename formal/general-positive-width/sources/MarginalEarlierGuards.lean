import MarginalNestedProjection
import MarginalOwnerFibers

namespace StackSorting.GraphWidth.MarginalA2.NestedSyntax
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy
variable {α : Type} {a colors : Nat}
variable (ats : {r : Nat} → InputAtom r → (Fin r → α) → Prop)

/-- Explicit endpoint guards prevent vacuous captured preorder on edge IDs
from entering the quantified intermediate-node and forest-root tests. -/
theorem earlier_vertices (u v : Fin a) (env : Fin a → α)
    (sets : Fin (CapturedLinkExtraction.parameterCount colors) → α → Prop)
    (h : ActualEval ats (earlier colors u v) env sets) :
    ats .vertex (fun _ => env u) ∧ ats .vertex (fun _ => env v) := ⟨h.1,h.2.1⟩

theorem earlier_owner (u v : Fin a) (env : Fin a → α)
    (sets : Fin (CapturedLinkExtraction.parameterCount colors) → α → Prop)
    (h : ActualEval ats (earlier colors u v) env sets) :
    ∃ owner, ats .owner (Fin.cases (env u) (fun _ => owner)) ∧
      ats .owner (Fin.cases (env v) (fun _ => owner)) := by
  obtain ⟨owner,hu,hv,_⟩ := h.2.2
  refine ⟨owner,?_,?_⟩
  · have he : (fun i : Fin 2 => Fin.cases owner env (pair u.succ 0 i))=
        Fin.cases (env u) (fun _ => owner) := by funext i; fin_cases i <;> rfl
    simpa only [ActualEval,binary,he] using hu
  · have he : (fun i : Fin 2 => Fin.cases owner env (pair v.succ 0 i))=
        Fin.cases (env v) (fun _ => owner) := by funext i; fin_cases i <;> rfl
    simpa only [ActualEval,binary,he] using hv

#print axioms earlier_vertices
#print axioms earlier_owner
end StackSorting.GraphWidth.MarginalA2.NestedSyntax
