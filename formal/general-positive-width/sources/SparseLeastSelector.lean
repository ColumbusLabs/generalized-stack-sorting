import SparseChoiceComparison
import SparseMonadicBlock

namespace StackSorting.SparseEndpointMSO.CanonicalChoice

/-- Extensional lexicographic comparison on the actual finite graph domain. -/
def BeforeSets (D : Model) (before : Formula 2 0)
    (A B : Fin k → Nat → Prop) : Prop :=
  ∃ i, (∀ j, j < i → ∀ x ∈ D.domain, (A j x ↔ B j x)) ∧
    ∃ p ∈ D.domain, (¬ A i p ∧ B i p) ∧
      ∀ q ∈ D.domain, OrderEval D before q p → (A i q ↔ B i q)

/-- Keep exactly an admissible tuple with no strictly earlier admissible tuple.
Both the candidate tuple and every competing tuple are ordinary monadic values;
no uniqueness, finite automaton or decomposition is postulated. -/
def leastSelector (before : Formula 2 0) (f : Formula 0 k) : Formula 0 k :=
  .conj f (allSets k (.implies
    (f.reindex id (Fin.castAdd k))
    (.neg (tupleBefore before (Fin.castAdd k) (Fin.natAdd k)))))

theorem eval_leastSelector (D : Model) (before : Formula 2 0)
    (f : Formula 0 k) (X : Fin k → Nat → Prop) :
    Eval D (leastSelector before f) Fin.elim0 X ↔
      Eval D f Fin.elim0 X ∧
        ∀ Y, SupportedTuple D Y → Eval D f Fin.elim0 Y →
          ¬ BeforeSets D before Y X := by
  rw [leastSelector, eval_conj', eval_allSets]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro Y
  apply imp_congr_right
  intro _
  simp only [Eval, Formula.eval_reindex, id_eq]
  have hy : (fun i => Fin.addCases Y X (Fin.castAdd k i)) = Y := by
    funext i
    exact Fin.addCases_left i
  rw [hy, eval_tupleBefore]
  simp only [Fin.addCases_left, Fin.addCases_right, BeforeSets]

#print axioms eval_leastSelector
end StackSorting.SparseEndpointMSO.CanonicalChoice
