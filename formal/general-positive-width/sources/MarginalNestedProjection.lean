import MarginalNestedSyntax

namespace StackSorting.GraphWidth.MarginalA2.NestedSyntax
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership
variable {α : Type}
variable (ats : {r : Nat} → InputAtom r → (Fin r → α) → Prop)

def incidenceAtoms : {r : Nat} → IncidenceAtom r → (Fin r → α) → Prop
  | _, .vertex, env => ats .vertex env
  | _, .edge, env => ats .localEdge env
  | _, .incidence, env => ats .incidence env
  | _, .insert, _ => False
  | _, .remove, _ => False

def ownerRelation (owner member : α) : Prop := ats .owner (Fin.cases member (fun _ => owner))

/-- Signature projection preserves every binder without changing parameters.
The owner predicate is a literal marginal-output atom in reversed order. -/
theorem eval_project (p : CopyFormula (OwnerMerge.Atom IncidenceAtom) a b)
    (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval ats (project p) env sets ↔
      ActualEval (OwnerMerge.atoms (incidenceAtoms ats) (ownerRelation ats)) p env sets := by
  induction p with
  | truth => rfl
  | equal => rfl
  | member => rfl
  | atom a args =>
    cases a with
    | loc a => cases a <;> simp [project,ActualEval,OwnerMerge.atoms,incidenceAtoms]
    | belongs =>
      simp only [project,ActualEval,OwnerMerge.atoms,ownerRelation]
      have he : (fun i : Fin 2 => env (args (if i=0 then 1 else 0)))=
          Fin.cases (env (args 1)) (fun _ => env (args 0)) := by
        funext i; fin_cases i <;> rfl
      rw [he]
  | neg p ih => exact not_congr (ih env sets)
  | conj p q ihp ihq => exact and_congr (ihp env sets) (ihq env sets)
  | implies p q ihp ihq => exact imp_congr (ihp env sets) (ihq env sets)
  | existsFO p ih => exact exists_congr (fun x => ih (Fin.cases x env) sets)
  | allFO p ih => exact forall_congr' (fun x => ih (Fin.cases x env) sets)
  | allSet p ih => exact forall_congr' (fun X => ih env (Fin.cases X sets))

/-- Reuse the checked owner-fiber theorem after the explicit signature map.
This includes capture avoidance through both kinds of nested binder. -/
theorem eval_project_relativize (owner : α) (p : CopyFormula IncidenceAtom a b)
    (vars : Fin a → Fin m) (anchor : Fin m) (env : Fin m → α)
    (localEnv : Fin a → OwnerMerge.Fiber (ownerRelation ats) owner)
    (sets : Fin b → α → Prop)
    (localSets : Fin b → OwnerMerge.Fiber (ownerRelation ats) owner → Prop)
    (ha : env anchor=owner) (hv : ∀ i, env (vars i)=(localEnv i).val)
    (hs : ∀ j v, sets j v.val ↔ localSets j v) :
    ActualEval ats (project (OwnerMerge.relativize p vars anchor)) env sets ↔
      ActualEval (OwnerMerge.fiberAtoms (incidenceAtoms ats) (ownerRelation ats) owner) p localEnv localSets :=
  (eval_project ats _ env sets).trans
    (OwnerMerge.eval_relativize (incidenceAtoms ats) (ownerRelation ats) owner p vars anchor env localEnv sets localSets ha hv hs)

#print axioms eval_project
#print axioms eval_project_relativize
end StackSorting.GraphWidth.MarginalA2.NestedSyntax
