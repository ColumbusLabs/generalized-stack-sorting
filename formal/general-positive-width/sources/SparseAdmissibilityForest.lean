import SparseFrontierAdmissibility
import EliminationForestFromDecomposition

namespace StackSorting.SparseEndpointMSO.EliminationSyntax
open SameVertexForest GraphWidth
variable {n k : Nat}

/-- Exact membership of the constructed same-vertex elimination frontier. -/
theorem named_frontier_iff (D : Model) (e : Fin n ≃ {x // x ∈ D.domain})
    (earlier : Formula 2 k) (X : Fin k → Nat → Prop) (ho : ModelForestOrder D earlier X)
    (H : Graph n) (hH : ∀ u v, H.Adj u v ↔ ModelAdjacent D (e u).val (e v).val)
    (v u : Fin n) :
    let O := namedStrictForestOrder D e earlier X ho
    ModelFrontier D earlier X (e v).val (e u).val ↔
      EliminationFrontier O.ranked.forest H v u := by
  let O := namedStrictForestOrder D e earlier X ho
  change ModelFrontier D earlier X (e v).val (e u).val ↔
    EliminationFrontier O.ranked.forest H v u
  constructor
  · rintro (he | ⟨huv,z,hz,hw,ha⟩)
    · exact Or.inl (e.injective (Subtype.ext he))
    · let w := e.symm ⟨z,hz⟩
      have he : e w=⟨z,hz⟩ := e.apply_symm_apply _
      have hr : O.rel u v := huv
      refine Or.inr ⟨(O.ranked_ancestor_iff u v).mpr (Or.inl hr),?_,w,?_,?_⟩
      · intro eq; subst u; exact O.irrefl v hr
      · apply (O.ranked_ancestor_iff v w).mpr
        rcases hw with hw | hw
        · exact Or.inr (e.injective (Subtype.ext (by simpa only [he] using hw)))
        · exact Or.inl (by simpa only [O,namedStrictForestOrder,he] using hw)
      · apply (hH u w).mpr
        simpa only [he] using ha
  · rintro (he | ⟨huv,hne,w,hw,ha⟩)
    · exact Or.inl (congrArg (fun i => (e i).val) he)
    · have hr := ((O.ranked_ancestor_iff u v).mp huv).resolve_right hne
      refine Or.inr ⟨hr,(e w).val,(e w).property,?_,(hH u w).mp ha⟩
      rcases (O.ranked_ancestor_iff v w).mp hw with h | h
      · exact Or.inr h
      · exact Or.inl (congrArg (fun i => (e i).val) h)

/-- A literal admissibility witness gives an actual same-vertex parent forest,
edge coverage and a numerical frontier bound. No decomposition, parent map,
rank or cardinality certificate is a premise. -/
theorem admissibleSentence_constructs_forest (D : Model)
    (e : Fin n ≃ {x // x ∈ D.domain}) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) (b : Nat)
    (hs : Eval D (admissibleSentence earlier b) Fin.elim0 X)
    (H : Graph n) (hH : ∀ u v, H.Adj u v ↔ ModelAdjacent D (e u).val (e v).val) :
    ∃ O : StrictForestOrder n,
      (∀ u v, O.rel u v ↔ RelationEval D earlier X (e u).val (e v).val) ∧
      (∀ u v, H.Adj u v → Ancestor O.ranked.forest u v ∨ Ancestor O.ranked.forest v u) ∧
      ∀ v, (eliminationFrontierSet O.ranked.forest H v).card ≤ b := by
  have ho := (eval_forestOrderSentence D earlier X).mp hs.1
  let O := namedStrictForestOrder D e earlier X ho
  refine ⟨O,fun _ _ => Iff.rfl,?_,?_⟩
  · intro u v huv
    have hh := (eval_eliminationSentence D earlier X).mp hs.2.1
      (e u).val (e u).property (e v).val (e v).property ((hH u v).mp huv)
    rcases hh with he | hu | hv
    · exact Or.inl ((O.ranked_ancestor_iff u v).mpr (Or.inr (e.injective (Subtype.ext he))))
    · exact Or.inl ((O.ranked_ancestor_iff u v).mpr (Or.inl hu))
    · exact Or.inr ((O.ranked_ancestor_iff v u).mpr (Or.inl hv))
  · intro v
    have hn := (eval_frontierBoundSentence D earlier X b).mp hs.2.2 (e v).val (e v).property
    have hr : FiniteTupleBound.Repeats (fun u => ModelFrontier D earlier X (e v).val (e u).val) b := by
      intro f hf hinj
      apply hn
      refine ⟨fun i => (e (f i)).val,fun i => (e (f i)).property,hf,?_⟩
      intro i j he
      exact hinj (e.injective (Subtype.ext he))
    have hc := (FiniteTupleBound.repeats_iff_card_le _ b).mp hr
    have heq : FiniteTupleBound.points (fun u => ModelFrontier D earlier X (e v).val (e u).val)=
        eliminationFrontierSet O.ranked.forest H v := by
      classical
      ext u
      simp only [FiniteTupleBound.mem_points,eliminationFrontierSet,Finset.mem_filter,
        Finset.mem_univ,true_and]
      exact named_frontier_iff D e earlier X ho H hH v u
    rwa [heq] at hc

#print axioms named_frontier_iff
#print axioms admissibleSentence_constructs_forest
end StackSorting.SparseEndpointMSO.EliminationSyntax
