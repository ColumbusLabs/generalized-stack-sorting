import FiniteForestOrderRank
import SparseEliminationSyntax

namespace StackSorting.SparseEndpointMSO.EliminationSyntax
open SameVertexForest
variable {k n : Nat}

/-- Literal first-order axioms for a strict forest order. Only the fixed input
relation formula is substituted; no binary relation is quantified. -/
def forestOrderSentence (earlier : Formula 2 k) : Formula 0 k :=
  .conj (.allFO 1 (.neg (relationAt earlier 0 0)))
    (.conj (.allFO 1 (.allFO 1 (.allFO 1
      (.implies (.conj (relationAt earlier 2 1) (relationAt earlier 1 0))
        (relationAt earlier 2 0)))))
      (.allFO 1 (.allFO 1 (.allFO 1
        (.implies (.conj (relationAt earlier 2 0) (relationAt earlier 1 0))
          (disjunction (relationAt earlier 2 1)
            (disjunction (.equal 2 1) (relationAt earlier 1 2))))))))

def ModelForestOrder (D : Model) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) : Prop :=
  (∀ x ∈ D.domain, ¬ RelationEval D earlier X x x) ∧
  (∀ x ∈ D.domain, ∀ y ∈ D.domain, ∀ z ∈ D.domain,
    RelationEval D earlier X x y → RelationEval D earlier X y z →
      RelationEval D earlier X x z) ∧
  (∀ x ∈ D.domain, ∀ y ∈ D.domain, ∀ z ∈ D.domain,
    RelationEval D earlier X x z → RelationEval D earlier X y z →
      RelationEval D earlier X x y ∨ x=y ∨ RelationEval D earlier X y x)

theorem eval_forestOrderSentence (D : Model) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) :
    Eval D (forestOrderSentence earlier) Fin.elim0 X ↔ ModelForestOrder D earlier X := by
  simp only [forestOrderSentence,eval_conj',eval_all_one,eval_neg',eval_implies',
    eval_relationAt,eval_disjunction]
  simp [Eval,Fin.addCases,ModelForestOrder,and_imp]

/-- The actual finite predecessor count produces a parent forest from the
literal first-order sentence. Names may be arbitrary and domain entries may
repeat; the equivalence is with the membership carrier. -/
noncomputable def namedStrictForestOrder (D : Model)
    (e : Fin n ≃ {x // x ∈ D.domain}) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop) (h : ModelForestOrder D earlier X) : StrictForestOrder n where
  rel u v := RelationEval D earlier X (e u).val (e v).val
  irrefl u := h.1 (e u).val (e u).property
  trans {u v w} hu hv := h.2.1 _ (e u).property _ (e v).property _ (e w).property hu hv
  predecessors {u v w} hu hv := by
    rcases h.2.2 _ (e u).property _ (e v).property _ (e w).property hu hv with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (e.injective (Subtype.ext h)))
    · exact Or.inr (Or.inr h)

/-- The original explicit cover formula names exactly the actual nonroot
parent links. Finite well-foundedness and the parent are conclusions. -/
theorem forestOrderSentence_parent_exact (D : Model)
    (e : Fin n ≃ {x // x ∈ D.domain}) (earlier : Formula 2 k)
    (X : Fin k → Nat → Prop)
    (hs : Eval D (forestOrderSentence earlier) Fin.elim0 X) (u v : Fin n) :
    let O := namedStrictForestOrder D e earlier X ((eval_forestOrderSentence D earlier X).mp hs)
    RelationEval D (coverFormula earlier) X (e u).val (e v).val ↔
      O.ranked.parent v=u ∧ u≠v := by
  let O := namedStrictForestOrder D e earlier X ((eval_forestOrderSentence D earlier X).mp hs)
  change RelationEval D (coverFormula earlier) X (e u).val (e v).val ↔
    O.ranked.parent v=u ∧ u≠v
  rw [eval_coverFormula]
  have cover : (RelationEval D earlier X (e u).val (e v).val ∧
      ¬ ∃ z ∈ D.domain, RelationEval D earlier X (e u).val z ∧
        RelationEval D earlier X z (e v).val) ↔ O.ranked.Cover u v := by
    apply and_congr_right
    intro _
    apply not_congr
    constructor
    · rintro ⟨z,hz,hu,hv⟩
      let w := e.symm ⟨z,hz⟩
      have he : e w=⟨z,hz⟩ := e.apply_symm_apply _
      exact ⟨w,by simpa only [O,namedStrictForestOrder,StrictForestOrder.ranked,he] using hu,
        by simpa only [O,namedStrictForestOrder,StrictForestOrder.ranked,he] using hv⟩
    · rintro ⟨w,hu,hv⟩
      exact ⟨(e w).val,(e w).property,hu,hv⟩
  rw [cover]
  constructor
  · intro hc
    have hn : u≠v := by
      intro h; subst u; exact O.irrefl v hc.1
    exact ⟨(O.ranked.parent_eq_iff_cover hn).mpr hc,hn⟩
  · rintro ⟨hp,hn⟩
    exact (O.ranked.parent_eq_iff_cover hn).mp hp

#print axioms eval_forestOrderSentence
#print axioms forestOrderSentence_parent_exact
end StackSorting.SparseEndpointMSO.EliminationSyntax
