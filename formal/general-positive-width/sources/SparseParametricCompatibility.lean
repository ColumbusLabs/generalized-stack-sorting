import SparseParametricFiniteCopy

namespace StackSorting.SparseEndpointMSO.FiniteCopy.Parametric

def ofPlain (J : FiniteCopy.Interpretation Atom c) : Interpretation Atom c 0 where
  domain := J.domain
  atom := J.atom

/-- The previous zero-parameter semantics is exactly the d=0 instance, for
all formula shapes, including zero copies and nested individual/set binders. -/
theorem copyEval_ofPlain (J : FiniteCopy.Interpretation Atom c) (D : Model)
    (params : Fin 0 → Nat → Prop) (p : CopyFormula Atom a b)
    (env : Fin a → Element c) (sets : Fin b → Element c → Prop) :
    CopyEval (ofPlain J) D params p env sets ↔ FiniteCopy.CopyEval J D p env sets := by
  have hp : params = Fin.elim0 := by funext i; exact Fin.elim0 i
  subst params
  induction p with
  | truth => rfl
  | equal => rfl
  | member => rfl
  | atom => rfl
  | neg p ih => exact not_congr (ih env sets)
  | conj p q ihp ihq => exact and_congr (ihp env sets) (ihq env sets)
  | implies p q ihp ihq => exact imp_congr (ihp env sets) (ihq env sets)
  | existsFO p ih => exact exists_congr (fun x => and_congr Iff.rfl (ih (Fin.cases x env) sets))
  | allFO p ih => exact forall_congr' (fun x => imp_congr Iff.rfl (ih (Fin.cases x env) sets))
  | allSet p ih => exact forall_congr' (fun X => imp_congr Iff.rfl (ih env (Fin.cases X sets)))

theorem eval_compile_ofPlain (J : FiniteCopy.Interpretation Atom c) (D : Model)
    (p : CopyFormula Atom a b) (tags : Fin a → Fin c) (vars : Fin a → Fin n)
    (map : Fin b → Fin c → Fin m) (params : Fin 0 → Fin m)
    (env : Fin n → Nat) (sets : Fin m → Nat → Prop) :
    Eval D (compile (ofPlain J) p tags vars map params) env sets ↔
      Eval D (FiniteCopy.compile J p tags vars map) env sets :=
  (eval_compile (ofPlain J) D p tags vars map params env sets).trans
    ((copyEval_ofPlain J D _ p _ _).trans
      (FiniteCopy.eval_compile J D p tags vars map env sets).symm)

#print axioms copyEval_ofPlain
#print axioms eval_compile_ofPlain
end StackSorting.SparseEndpointMSO.FiniteCopy.Parametric
