import OwnerParameterMerge

namespace StackSorting.SparseEndpointMSO.FiniteCopy.OwnerMerge
variable {LocalAtom : Nat → Type} {α : Type}
variable (loc : {r : Nat} → LocalAtom r → (Fin r → α) → Prop)
variable (belongs : α → α → Prop)

/-- Relativized formulas depend only on the values of their named free
variables and owner, even when the ambient variable contexts differ. -/
theorem eval_relativize_values (p : CopyFormula LocalAtom a b)
    (vars : Fin a → Fin m) (vars' : Fin a → Fin n) (anchor : Fin m) (anchor' : Fin n)
    (env : Fin m → α) (env' : Fin n → α) (sets : Fin b → α → Prop)
    (ha : env anchor=env' anchor') (hv : ∀ i, env (vars i)=env' (vars' i)) :
    ActualEval (atoms loc belongs) (relativize p vars anchor) env sets ↔
      ActualEval (atoms loc belongs) (relativize p vars' anchor') env' sets := by
  induction p generalizing m n with
  | truth => rfl
  | equal i j => simp only [relativize,ActualEval,hv]
  | member i j => simp only [relativize,ActualEval,hv]
  | atom a args =>
    simp only [relativize,ActualEval,atoms]
    have he : (fun i => env (vars (args i)))=(fun i => env' (vars' (args i))) :=
      funext (fun i => hv (args i))
    rw [he]
  | neg p ih => exact not_congr (ih vars vars' anchor anchor' env env' sets ha hv)
  | conj p q ihp ihq =>
    exact and_congr (ihp vars vars' anchor anchor' env env' sets ha hv)
      (ihq vars vars' anchor anchor' env env' sets ha hv)
  | implies p q ihp ihq =>
    exact imp_congr (ihp vars vars' anchor anchor' env env' sets ha hv)
      (ihq vars vars' anchor anchor' env env' sets ha hv)
  | existsFO p ih =>
    simp only [relativize,ActualEval,eval_guard]
    apply exists_congr
    intro x
    apply and_congr
    · simp only [Fin.cases_succ,Fin.cases_zero,ha]
    · exact ih (Fin.cases 0 (fun i => (vars i).succ)) (Fin.cases 0 (fun i => (vars' i).succ))
        anchor.succ anchor'.succ (Fin.cases x env) (Fin.cases x env') sets (by simpa only [Fin.cases_succ] using ha)
        (fun i => Fin.cases rfl hv i)
  | allFO p ih =>
    simp only [relativize,ActualEval,eval_guard]
    apply forall_congr'
    intro x
    apply imp_congr
    · simp only [Fin.cases_succ,Fin.cases_zero,ha]
    · exact ih (Fin.cases 0 (fun i => (vars i).succ)) (Fin.cases 0 (fun i => (vars' i).succ))
        anchor.succ anchor'.succ (Fin.cases x env) (Fin.cases x env') sets (by simpa only [Fin.cases_succ] using ha)
        (fun i => Fin.cases rfl hv i)
  | allSet p ih =>
    exact forall_congr' (fun X => ih vars vars' anchor anchor' env env' (Fin.cases X sets) ha hv)

#print axioms eval_relativize_values
end StackSorting.SparseEndpointMSO.FiniteCopy.OwnerMerge
