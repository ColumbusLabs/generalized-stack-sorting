import PhysicalModelLeastSelector
import SparseEliminationSyntax

namespace StackSorting.SparseEndpointMSO.CanonicalChoice
open EliminationSyntax
variable {a k : Nat}

/-- Existential closure of a fixed finite tuple of supported monadic sets.
The number of quantifiers is the fixed formula parameter k. -/
def existsSetTuple (f : Formula a k) : Formula a 0 :=
  .neg (allSets k (.neg f))

theorem eval_existsSetTuple (D : Model) (f : Formula a k) (env : Fin a → Nat) :
    Eval D (existsSetTuple f) env Fin.elim0 ↔
      ∃ X, SupportedTuple D X ∧ Eval D f env X := by
  classical
  rw [existsSetTuple,eval_neg',eval_allSets]
  have he (X : Fin k → Nat → Prop) : (Fin.addCases (m := k) (n := 0) (motive := fun _ => Nat → Prop) X Fin.elim0)=X := by
    funext i
    exact Fin.addCases_left i
  simp only [eval_neg',he,not_forall,not_not]
  constructor
  · rintro ⟨X,hX,hf⟩; exact ⟨X,hX,hf⟩
  · rintro ⟨X,hX,hf⟩; exact ⟨X,hX,hf⟩

/-- Extract a relation from the unique least admissible tuple. The tuple is
quantified inside the sentence, rather than stored in the binary alphabet. -/
def selectedRelation (admissible : Formula 0 k) (relation : Formula 2 k) : Formula 2 0 :=
  existsSetTuple (.conj ((leastSelector chronologicalBefore admissible).reindex Fin.elim0 id) relation)

theorem eval_selectedRelation (D : Model) (admissible : Formula 0 k)
    (relation : Formula 2 k) (x y : Nat) :
    RelationEval D (selectedRelation admissible relation) Fin.elim0 x y ↔
      ∃ X, SupportedTuple D X ∧
        Eval D (leastSelector chronologicalBefore admissible) Fin.elim0 X ∧
        RelationEval D relation X x y := by
  rw [RelationEval,selectedRelation,eval_existsSetTuple]
  apply exists_congr
  intro X
  simp only [eval_conj',Formula.eval_reindex,id_eq]
  have he : (fun i : Fin 0 => pairEnv x y (Fin.elim0 i))=Fin.elim0 := by
    funext i; exact Fin.elim0 i
  rw [he]
  rfl

/-- On an accepted physical model the selected relation is exactly the
relation of its actual least supported witness, with no additional sets. -/
theorem physical_selectedRelation_exact {D : Model} {r s : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (admissible : Formula 0 k) (relation : Formula 2 k)
    (X : Fin k → Nat → Prop) (hX : SupportedTuple D X)
    (hx : Eval D (leastSelector chronologicalBefore admissible) Fin.elim0 X)
    (x y : Nat) :
    RelationEval D (selectedRelation admissible relation) Fin.elim0 x y ↔
      RelationEval D relation X x y := by
  rw [eval_selectedRelation]
  constructor
  · rintro ⟨Y,hY,hy,hr⟩
    have hadm := ((eval_leastSelector D chronologicalBefore admissible X).mp hx).1
    obtain ⟨Z,_hz,hu⟩ := physicalModel_exists_unique_leastSelector hD admissible ⟨X,hX,hadm⟩
    have he : Y=X := (hu Y ⟨hY,hy⟩).trans (hu X ⟨hX,hx⟩).symm
    simpa only [he] using hr
  · intro hr
    exact ⟨X,hX,hx,hr⟩

/-- The proper selected parent is a fixed sparse MSO formula with two free
vertices and no free set parameters. Admissibility existence remains a
separate theorem obligation. -/
def selectedParent (admissible : Formula 0 k) (earlier : Formula 2 k) : Formula 2 0 :=
  selectedRelation admissible (coverFormula earlier)

#print axioms eval_existsSetTuple
#print axioms eval_selectedRelation
#print axioms physical_selectedRelation_exact
end StackSorting.SparseEndpointMSO.CanonicalChoice
