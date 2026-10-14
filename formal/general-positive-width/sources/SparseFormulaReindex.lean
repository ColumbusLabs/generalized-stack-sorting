import SparseEndpointMSO

/-! Capture-avoiding index reindexing for the original sparse graph MSO.
This changes variable names only and adds no predicates or semantic oracle. -/
namespace StackSorting.SparseEndpointMSO

/-- Rename free individual and monadic indices; fresh binders stay fixed. -/
def Formula.reindex : Formula a b → (Fin a → Fin c) → (Fin b → Fin d) → Formula c d
  | .truth, _, _ => .truth
  | .equal i j, f, _ => .equal (f i) (f j)
  | .member i X, f, g => .member (f i) (g X)
  | .insert i, f, _ => .insert (f i)
  | .remove i, f, _ => .remove (f i)
  | .successor i j, f, _ => .successor (f i) (f j)
  | .matching i j, f, _ => .matching (f i) (f j)
  | .neg p, f, g => .neg (p.reindex f g)
  | .conj p q, f, g => .conj (p.reindex f g) (q.reindex f g)
  | .implies p q, f, g => .implies (p.reindex f g) (q.reindex f g)
  | .existsFO k p, f, g => .existsFO k (p.reindex
      (Fin.addCases (Fin.castAdd c) (fun i => Fin.natAdd k (f i))) g)
  | .allFO k p, f, g => .allFO k (p.reindex
      (Fin.addCases (Fin.castAdd c) (fun i => Fin.natAdd k (f i))) g)
  | .allSet p, f, g => .allSet (p.reindex f (Fin.cases 0 (fun i => (g i).succ)))

theorem Formula.eval_reindex (D : Model) (p : Formula a b)
    (f : Fin a → Fin c) (g : Fin b → Fin d)
    (env : Fin c → Nat) (sets : Fin d → Nat → Prop) :
    Eval D (p.reindex f g) env sets ↔
      Eval D p (fun i => env (f i)) (fun X => sets (g X)) := by
  induction p generalizing c d with
  | truth => rfl
  | equal => rfl
  | member => rfl
  | insert => rfl
  | remove => rfl
  | successor => rfl
  | matching => rfl
  | neg p ih => exact not_congr (ih f g env sets)
  | conj p q ihp ihq => exact and_congr (ihp f g env sets) (ihq f g env sets)
  | implies p q ihp ihq => exact imp_congr (ihp f g env sets) (ihq f g env sets)
  | existsFO k p ih =>
    simp only [Formula.reindex, Eval]
    apply exists_congr
    intro values
    apply and_congr_right
    intro _
    rw [ih]
    have he : (fun i => Fin.addCases values env
        (Fin.addCases (Fin.castAdd c) (fun j => Fin.natAdd k (f j)) i)) =
        Fin.addCases values (fun i => env (f i)) := by
      funext i
      exact Fin.addCases (fun j => by simp) (fun j => by simp) i
    rw [he]
  | allFO k p ih =>
    simp only [Formula.reindex, Eval]
    apply forall_congr'
    intro values
    apply imp_congr_right
    intro _
    rw [ih]
    have he : (fun i => Fin.addCases values env
        (Fin.addCases (Fin.castAdd c) (fun j => Fin.natAdd k (f j)) i)) =
        Fin.addCases values (fun i => env (f i)) := by
      funext i
      exact Fin.addCases (fun j => by simp) (fun j => by simp) i
    rw [he]
  | allSet p ih =>
    simp only [Formula.reindex, Eval]
    apply forall_congr'
    intro X
    apply imp_congr_right
    intro _
    rw [ih]
    have he : (fun i => Fin.cases X sets (Fin.cases 0 (fun j => (g j).succ) i)) =
        Fin.cases X (fun i => sets (g i)) := by
      funext i
      exact Fin.cases (by simp) (fun j => by simp) i
    rw [he]

#print axioms Formula.eval_reindex
end StackSorting.SparseEndpointMSO
