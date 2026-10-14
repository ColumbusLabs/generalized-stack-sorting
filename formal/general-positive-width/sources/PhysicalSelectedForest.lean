import SparseAdmissibilityForest
import SparseSelectedRelation

namespace StackSorting.SparseEndpointMSO.CanonicalChoice
open EliminationSyntax SameVertexForest GraphWidth
variable {n k : Nat}

/-- Existential admissibility on an actual physical model produces a concrete
bounded parent forest whose proper parent relation is fixed by a set-free
literal MSO formula. Existence of an admissible tuple is explicit. -/
theorem physical_exists_selected_forest {D : Model} {r s : Nat}
    (hD : Satisfies D (fullAcceptedSentence r s))
    (e : Fin n ≃ {x // x ∈ D.domain}) (earlier : Formula 2 k) (b : Nat)
    (H : Graph n) (hH : ∀ u v, H.Adj u v ↔ ModelAdjacent D (e u).val (e v).val)
    (hex : ∃ X, SupportedTuple D X ∧ Eval D (admissibleSentence earlier b) Fin.elim0 X) :
    ∃ O : StrictForestOrder n,
      (∀ u v, RelationEval D (selectedParent (admissibleSentence earlier b) earlier)
        Fin.elim0 (e u).val (e v).val ↔ O.ranked.parent v=u ∧ u≠v) ∧
      (∀ u v, H.Adj u v → Ancestor O.ranked.forest u v ∨ Ancestor O.ranked.forest v u) ∧
      ∀ v, (eliminationFrontierSet O.ranked.forest H v).card ≤ b := by
  let f := admissibleSentence earlier b
  obtain ⟨X,⟨hX,hx⟩,_hu⟩ := physicalModel_exists_unique_leastSelector hD f hex
  have hadm := ((eval_leastSelector D chronologicalBefore f X).mp hx).1
  obtain ⟨O,hrel,hedge,hbound⟩ := admissibleSentence_constructs_forest D e earlier X b hadm H hH
  refine ⟨O,?_,hedge,hbound⟩
  intro u v
  rw [selectedParent,physical_selectedRelation_exact hD f (coverFormula earlier) X hX hx]
  rw [eval_coverFormula,←hrel u v]
  have hc : (¬ ∃ z ∈ D.domain, RelationEval D earlier X (e u).val z ∧
      RelationEval D earlier X z (e v).val) ↔ ¬ ∃ w, O.rel u w ∧ O.rel w v := by
    apply not_congr
    constructor
    · rintro ⟨z,hz,hu,hv⟩
      let w := e.symm ⟨z,hz⟩
      have he : e w=⟨z,hz⟩ := e.apply_symm_apply _
      refine ⟨w,(hrel u w).mpr ?_,(hrel w v).mpr ?_⟩
      · simpa only [he] using hu
      · simpa only [he] using hv
    · rintro ⟨w,hu,hv⟩
      exact ⟨(e w).val,(e w).property,(hrel u w).mp hu,(hrel w v).mp hv⟩
  rw [hc]
  constructor
  · intro h
    have hn : u≠v := by intro he; subst u; exact O.irrefl v h.1
    exact ⟨(O.ranked_parent_iff_cover hn).mpr h,hn⟩
  · rintro ⟨hp,hn⟩
    exact (O.ranked_parent_iff_cover hn).mp hp

#print axioms physical_exists_selected_forest
end StackSorting.SparseEndpointMSO.CanonicalChoice
