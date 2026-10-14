import SparseForestOrderAdmissibility
import FiniteTupleCardinality

namespace StackSorting.SparseEndpointMSO.EliminationSyntax
variable {k : Nat}

/-- All directions of the actual sparse S/M relations, with no reachability
or decomposition relation introduced as a new atom. -/
def sparseAdjacent : Formula 2 k :=
  disjunction (.successor 0 1) (disjunction (.successor 1 0)
    (disjunction (.matching 0 1) (.matching 1 0)))

def ModelAdjacent (D : Model) (x y : Nat) : Prop :=
  D.S x y ∨ D.S y x ∨ D.M x y ∨ D.M y x

theorem eval_sparseAdjacent (D : Model) (X : Fin k → Nat → Prop) (x y : Nat) :
    RelationEval D sparseAdjacent X x y ↔ ModelAdjacent D x y := by
  simp only [RelationEval,sparseAdjacent,eval_disjunction,ModelAdjacent]
  rfl

/-- Every actual sparse edge has comparable endpoints in the strict order. -/
def eliminationSentence (earlier : Formula 2 k) : Formula 0 k :=
  .allFO 1 (.allFO 1 (.implies (relationAt sparseAdjacent 1 0)
    (disjunction (.equal 1 0)
      (disjunction (relationAt earlier 1 0) (relationAt earlier 0 1)))))

theorem eval_eliminationSentence (D : Model) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) :
    Eval D (eliminationSentence earlier) Fin.elim0 X ↔
      ∀ x ∈ D.domain, ∀ y ∈ D.domain, ModelAdjacent D x y →
        x=y ∨ RelationEval D earlier X x y ∨ RelationEval D earlier X y x := by
  simp only [eliminationSentence,eval_all_one,eval_implies',eval_relationAt,
    eval_sparseAdjacent,eval_disjunction]
  simp [Eval,Fin.addCases]

/-- The self vertex and the inherited strict-ancestor/descendant-neighbor
frontier, expressed solely with the supplied strict relation formula. -/
def frontierFormula (earlier : Formula 2 k) : Formula 2 k :=
  disjunction (.equal 1 0) (.conj (relationAt earlier 1 0)
    (.existsFO 1 (.conj (disjunction (.equal 1 0) (relationAt earlier 1 0))
      (relationAt sparseAdjacent 2 0))))

def ModelFrontier (D : Model) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) (v u : Nat) : Prop :=
  u=v ∨ RelationEval D earlier X u v ∧ ∃ z ∈ D.domain,
    (v=z ∨ RelationEval D earlier X v z) ∧ ModelAdjacent D u z

theorem eval_frontierFormula (D : Model) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) (v u : Nat) :
    RelationEval D (frontierFormula earlier) X v u ↔ ModelFrontier D earlier X v u := by
  change Eval D (frontierFormula earlier) (pairEnv v u) X ↔ _
  simp only [frontierFormula,eval_disjunction,eval_conj',eval_exists_one,
    eval_relationAt,eval_sparseAdjacent]
  simp [Eval,Fin.addCases,pairEnv,ModelFrontier,Fin.cases]
  rfl

/-- Distinctness of the newly quantified tuple, retaining all old variables
and all set parameters without capture. -/
def distinctTuple (m a k : Nat) : Formula (m+a) k :=
  allFin (fun i : Fin m => allFin (fun j : Fin m =>
    if i=j then .truth else .neg (.equal (i.castAdd a) (j.castAdd a))))

theorem eval_distinctTuple (D : Model) (m a k : Nat)
    (values : Fin m → Nat) (env : Fin a → Nat) (X : Fin k → Nat → Prop) :
    Eval D (distinctTuple m a k) (Fin.addCases values env) X ↔
      Function.Injective values := by
  simp only [distinctTuple,eval_allFin]
  constructor
  · intro h i j he
    by_contra hn
    have hh := h i j
    simp only [ite_eq_right hn,Eval,Fin.addCases_left] at hh
    exact hh he
  · intro h i j
    split
    · trivial
    · rename_i hn
      simpa only [Eval,Fin.addCases_left] using (show values i ≠ values j from fun he => hn (h he))

def frontierBoundSentence (earlier : Formula 2 k) (b : Nat) : Formula 0 k :=
  .allFO 1 (.neg (.existsFO (b+1)
    (.conj (allFin (fun i : Fin (b+1) =>
      relationAt (frontierFormula earlier) (Fin.natAdd (b+1) (0 : Fin 1)) (i.castAdd 1)))
      (distinctTuple (b+1) 1 k))))

theorem eval_frontierBoundSentence (D : Model) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) (b : Nat) :
    Eval D (frontierBoundSentence earlier b) Fin.elim0 X ↔
      ∀ v ∈ D.domain, ¬ ∃ values : Fin (b+1) → Nat,
        (∀ i, values i ∈ D.domain) ∧
        (∀ i, ModelFrontier D earlier X v (values i)) ∧ Function.Injective values := by
  simp only [frontierBoundSentence,eval_all_one,eval_neg']
  apply forall_congr'
  intro v
  apply forall_congr'
  intro _
  apply not_congr
  change (∃ values : Fin (b+1) → Nat, (∀ i, values i ∈ D.domain) ∧ _) ↔ _
  apply exists_congr
  intro values
  simp only [eval_conj',eval_allFin,eval_relationAt,eval_frontierFormula,
    Fin.addCases_left,Fin.addCases_right,eval_distinctTuple]
  simp [Fin.addCases]

/-- Admissibility is one fixed-parameter literal MSO formula. It does not
quantify a parent relation or assume a decomposition witness. -/
def admissibleSentence (earlier : Formula 2 k) (b : Nat) : Formula 0 k :=
  .conj (forestOrderSentence earlier)
    (.conj (eliminationSentence earlier) (frontierBoundSentence earlier b))

#print axioms eval_eliminationSentence
#print axioms eval_frontierFormula
#print axioms eval_distinctTuple
#print axioms eval_frontierBoundSentence
end StackSorting.SparseEndpointMSO.EliminationSyntax
