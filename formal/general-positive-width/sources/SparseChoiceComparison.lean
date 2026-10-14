import SparseFormulaReindex
import SparseStructuralSentence

/-! Explicit finite sparse-MSO syntax comparing monadic witness tuples.
The order is supplied as two-variable syntax, not as an added atomic oracle. -/
namespace StackSorting.SparseEndpointMSO.CanonicalChoice

/-- Direct semantics of the supplied two-node order formula. -/
def OrderEval (D : Model) (before : Formula 2 0) (x y : Nat) : Prop :=
  Eval D before (Fin.cases x (fun _ => y)) Fin.elim0

def setEqual (i j : Fin b) : Formula 0 b :=
  .allFO 1 (equivalence (.member 0 i) (.member 0 j))

def setBefore (before : Formula 2 0) (i j : Fin b) : Formula 0 b :=
  .existsFO 1 (.conj (.conj (.neg (.member 0 i)) (.member 0 j))
    (.allFO 1 (.implies (before.reindex id Fin.elim0)
      (equivalence (.member 0 i) (.member 0 j)))))

def anyFin (fs : Fin k → Formula a b) : Formula a b :=
  .neg (allFin (fun i => .neg (fs i)))

def tupleBefore (before : Formula 2 0) (left right : Fin k → Fin b) : Formula 0 b :=
  anyFin (fun i => .conj
    (allFin (fun j => if j < i then setEqual (left j) (right j) else .truth))
    (setBefore before (left i) (right i)))

theorem eval_anyFin (D : Model) (fs : Fin k → Formula a b)
    (env : Fin a → Nat) (sets : Fin b → Nat → Prop) :
    Eval D (anyFin fs) env sets ↔ ∃ i, Eval D (fs i) env sets := by
  classical
  simp [anyFin, Eval, eval_allFin]

theorem eval_setEqual (D : Model) (i j : Fin b) (sets : Fin b → Nat → Prop) :
    Eval D (setEqual i j) Fin.elim0 sets ↔
      ∀ x ∈ D.domain, (sets i x ↔ sets j x) := by
  simp [setEqual, eval_all_one, eval_equivalence, Eval]

theorem eval_setBefore (D : Model) (before : Formula 2 0) (i j : Fin b)
    (sets : Fin b → Nat → Prop) :
    Eval D (setBefore before i j) Fin.elim0 sets ↔
      ∃ p ∈ D.domain, (¬ sets i p ∧ sets j p) ∧
        ∀ q ∈ D.domain, OrderEval D before q p → (sets i q ↔ sets j q) := by
  rw [setBefore, eval_exists_one]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  rw [eval_conj', eval_conj', eval_neg', eval_all_one]
  simp only [Eval, Formula.eval_reindex, eval_equivalence, id_eq]
  have he (q : Nat) :
      (fun u : Fin 2 => Fin.addCases (fun _ : Fin 1 => q)
        (fun j => Fin.addCases (fun _ : Fin 1 => p) Fin.elim0 j) u) =
        Fin.cases q (fun _ => p) := by
    funext u
    refine Fin.cases ?_ (fun j => ?_) u
    · rfl
    · have hj : j = 0 := by apply Fin.ext; omega
      subst j
      rfl
  have hs : (fun X : Fin 0 => sets X.elim0) = (Fin.elim0 : Fin 0 → Nat → Prop) := by
    funext X; exact Fin.elim0 X
  simp only [he, hs]
  rfl

theorem eval_tupleBefore (D : Model) (before : Formula 2 0)
    (left right : Fin k → Fin b) (sets : Fin b → Nat → Prop) :
    Eval D (tupleBefore before left right) Fin.elim0 sets ↔
      ∃ i, (∀ j, j < i → ∀ x ∈ D.domain, (sets (left j) x ↔ sets (right j) x)) ∧
        ∃ p ∈ D.domain, (¬ sets (left i) p ∧ sets (right i) p) ∧
          ∀ q ∈ D.domain, OrderEval D before q p →
            (sets (left i) q ↔ sets (right i) q) := by
  have he (i : Fin k) :
      Eval D (allFin (fun j => if j < i then setEqual (left j) (right j) else .truth))
        Fin.elim0 sets ↔
      ∀ j, j < i → ∀ x ∈ D.domain, (sets (left j) x ↔ sets (right j) x) := by
    rw [eval_allFin]
    constructor
    · intro h j hj
      have hh := h j
      rw [ite_eq_left hj, eval_setEqual] at hh
      exact hh
    · intro h j
      by_cases hj : j < i
      · rw [ite_eq_left hj, eval_setEqual]
        exact h j hj
      · rw [ite_eq_right hj]
        trivial
  simp only [tupleBefore, eval_anyFin, eval_conj', he, eval_setBefore]

#print axioms eval_tupleBefore
#print axioms eval_setEqual
#print axioms eval_setBefore
end StackSorting.SparseEndpointMSO.CanonicalChoice
