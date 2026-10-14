import MarginalSelectionValidity
import MarginalIncidenceSyntax
import ActualFormulaEquiv

namespace StackSorting.GraphWidth.MarginalA2.SelectionControls
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open FinitePort Nested

/-- The all-false tuple removes every synthetic candidate from the literal
copy domain, independently of the input atoms. -/
theorem empty_selector_domain_absent {V : Type} {W : Nat}
    (atoms : {r : Nat} → Syntax.InputAtom r → (Fin r → V) → Prop)
    (i j : Fin W) (env : Fin 1 → V) :
    ¬ ActualEval atoms (Syntax.domain (Syntax.fixed W) (.inr (i,j))) env
      (fun _ _ => False) := by
  exact fun h => h

/-- A genuine required extra edge has candidate endpoints, but the empty
selection has no selected candidate covering them. This is the positive
absence control paired with the false universal-coverage negative test. -/
theorem empty_selector_misses_required_edge
    {n t W : Nat} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (C : AdhesionColoring D W) (e : ExtraEdge D) :
    PairAt D C (chosenCandidate D C e) e.val.1 e.val.2 ∧
    ¬ ∃ q : Candidate t W, False ∧ CoversPair D C q e.val.1 e.val.2 := by
  exact ⟨chosen_pair D C e,fun ⟨_,h,_⟩ => h⟩

#print axioms empty_selector_domain_absent
#print axioms empty_selector_misses_required_edge
end StackSorting.GraphWidth.MarginalA2.SelectionControls
