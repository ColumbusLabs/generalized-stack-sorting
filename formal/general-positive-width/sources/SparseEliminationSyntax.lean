import PhysicalModelLeastSelector

namespace StackSorting.SparseEndpointMSO.EliminationSyntax
open _root_.StackSorting.SparseEndpointMSO.CanonicalChoice

def pairEnv (x y : Nat) : Fin 2 → Nat := Fin.cases x (fun _ => y)
def RelationEval (D : Model) (f : Formula 2 k) (X : Fin k → Nat → Prop) (x y : Nat) : Prop :=
  Eval D f (pairEnv x y) X

def relationAt (f : Formula 2 k) (i j : Fin a) : Formula a k :=
  f.reindex (Fin.cases i (fun _ => j)) id

theorem eval_relationAt (D : Model) (f : Formula 2 k) (i j : Fin a)
    (env : Fin a → Nat) (X : Fin k → Nat → Prop) :
    Eval D (relationAt f i j) env X ↔ RelationEval D f X (env i) (env j) := by
  rw [relationAt, Formula.eval_reindex]
  have he : (fun v => env (Fin.cases i (fun _ => j) v)) = pairEnv (env i) (env j) := by
    funext v
    exact Fin.cases rfl (fun _ => rfl) v
  rw [he]
  rfl

/-- Break simultaneous introduction ties with the definable physical chronology. -/
def splitPreorder (rho : Formula 2 k) : Formula 2 k :=
  .conj rho (disjunction (.neg (relationAt rho 1 0))
    (chronologicalBefore.reindex id Fin.elim0))

/-- The cover relation is explicit original sparse MSO with one bound vertex. -/
def coverFormula (earlier : Formula 2 k) : Formula 2 k :=
  .conj earlier (.neg (.existsFO 1 (.conj
    (relationAt earlier 1 0) (relationAt earlier 0 2))))

theorem eval_splitPreorder (D : Model) (rho : Formula 2 k)
    (X : Fin k → Nat → Prop) (x y : Nat) :
    RelationEval D (splitPreorder rho) X x y ↔
      RelationEval D rho X x y ∧
        (¬ RelationEval D rho X y x ∨ OrderEval D chronologicalBefore x y) := by
  simp only [RelationEval, splitPreorder, eval_conj', eval_disjunction, eval_neg',
    eval_relationAt, Formula.eval_reindex, pairEnv, Fin.cases_zero, id_eq]
  rfl

theorem eval_coverFormula (D : Model) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) (x y : Nat) :
    RelationEval D (coverFormula earlier) X x y ↔
      RelationEval D earlier X x y ∧
        ¬ ∃ z ∈ D.domain, RelationEval D earlier X x z ∧ RelationEval D earlier X z y := by
  simp only [RelationEval, coverFormula, eval_conj', eval_neg', eval_exists_one, eval_relationAt]
  rfl

#print axioms eval_splitPreorder
#print axioms eval_coverFormula
end StackSorting.SparseEndpointMSO.EliminationSyntax
