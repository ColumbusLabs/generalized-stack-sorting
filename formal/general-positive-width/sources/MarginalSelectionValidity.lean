import MarginalEdgeCodes

namespace StackSorting.GraphWidth.MarginalA2
open FinitePort Nested
variable {n t W : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (C : AdhesionColoring D W)

/-- Actual validity predicate corresponding to the literal candidate formula. -/
def PairAt (q : Candidate t W) (u v : Fin n) : Prop :=
  u≠v ∧ ¬G.Adj u v ∧ q.2.2.val≠0 ∧
    introductionNode D u=T.parent q.2.2 ∧ introductionNode D v=T.parent q.2.2 ∧
    outerAdhesion D q.2.2 u ∧ outerAdhesion D q.2.2 v ∧
    C.color u=q.1 ∧ C.color v=q.2.1

theorem chosen_pair (e : ExtraEdge D) :
    PairAt D C (chosenCandidate D C e) e.val.1 e.val.2 := by
  have h := chosenCandidate_spec D C e
  exact ⟨e.property.2.2.2.2.1,e.property.2.1,h.1,h.2.1.symm,
    (extra_same_owner D e).trans h.2.1.symm,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

theorem pair_functional {q : Candidate t W} {u v a b : Fin n}
    (h : PairAt D C q u v) (j : PairAt D C q a b) : u=a ∧ v=b := by
  exact ⟨C.separates _ _ _ h.2.2.2.2.2.1 j.2.2.2.2.2.1
      (h.2.2.2.2.2.2.2.1.trans j.2.2.2.2.2.2.2.1.symm),
    C.separates _ _ _ h.2.2.2.2.2.2.1 j.2.2.2.2.2.2.1
      (h.2.2.2.2.2.2.2.2.trans j.2.2.2.2.2.2.2.2.symm)⟩

theorem pair_has_edge {q : Candidate t W} {u v : Fin n} (h : PairAt D C q u v) :
    ∃ e : ExtraEdge D, e.val=(u,v) ∨ e.val=(v,u) := by
  have hne : u.val≠v.val := fun hh => h.1 (Fin.ext hh)
  rcases lt_or_gt_of_ne hne with huv | hvu
  · refine ⟨⟨(u,v),huv,h.2.1,?_⟩,Or.inl rfl⟩
    refine ⟨rfl,h.2.2.2.2.1.trans h.2.2.2.1.symm,h.1,Or.inr ?_⟩
    exact ⟨q.2.2,h.2.2.1,h.2.2.2.1.symm,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1⟩
  · refine ⟨⟨(v,u),hvu,?_,?_⟩,Or.inr rfl⟩
    · intro he; exact h.2.1 (G.symm he)
    · refine ⟨rfl,h.2.2.2.1.trans h.2.2.2.2.1.symm,h.1.symm,Or.inr ?_⟩
      exact ⟨q.2.2,h.2.2.1,h.2.2.2.2.1.symm,h.2.2.2.2.2.2.1,h.2.2.2.2.2.1⟩

def CoversPair (q : Candidate t W) (u v : Fin n) : Prop :=
  PairAt D C q u v ∨ PairAt D C q v u

theorem selected_sound {q : Candidate t W} (hq : selected D C q.1 q.2.1 q.2.2) :
    ∃ u v, PairAt D C q u v := by
  obtain ⟨e,he⟩ := hq
  change chosenCandidate D C e=q at he
  exact ⟨e.val.1,e.val.2,he ▸ chosen_pair D C e⟩

/-- Every actual missing pair gets a selected code, even when its original
candidate orientation is opposite to the carrier's mathematical pair order. -/
theorem selected_coverage {q : Candidate t W} {u v : Fin n} (h : PairAt D C q u v) :
    ∃ r : Candidate t W, selected D C r.1 r.2.1 r.2.2 ∧ CoversPair D C r u v := by
  obtain ⟨e,he | he⟩ := pair_has_edge D C h
  · refine ⟨chosenCandidate D C e,⟨e,rfl⟩,Or.inl ?_⟩
    have hp := chosen_pair D C e
    simpa only [he] using hp
  · refine ⟨chosenCandidate D C e,⟨e,rfl⟩,Or.inr ?_⟩
    have hp := chosen_pair D C e
    simpa only [he] using hp

/-- Two actual sorted missing-edge pairs with the same unordered endpoints
are equal. No code quotient is introduced. -/
theorem extra_unordered_ext {e f : ExtraEdge D}
    (h : (e.val.1=f.val.1 ∧ e.val.2=f.val.2) ∨
      (e.val.1=f.val.2 ∧ e.val.2=f.val.1)) : e=f := by
  rcases h with h | h
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · have he := e.property.1
    have hf := f.property.1
    rw [h.1,h.2] at he
    omega

/-- Uniqueness across child IDs, ordered-color tags, and either orientation. -/
theorem selected_unique {q r : Candidate t W} {u v : Fin n}
    (hq : selected D C q.1 q.2.1 q.2.2) (hr : selected D C r.1 r.2.1 r.2.2)
    (hquv : CoversPair D C q u v) (hruv : CoversPair D C r u v) : q=r := by
  obtain ⟨e,he⟩ := hq
  obtain ⟨f,hf⟩ := hr
  have pe := he ▸ chosen_pair D C e
  have pf := hf ▸ chosen_pair D C f
  have hef : e=f := by
    rcases hquv with hq | hq <;> rcases hruv with hr | hr
    · obtain ⟨h₁,h₂⟩ := pair_functional D C pe hq
      obtain ⟨h₃,h₄⟩ := pair_functional D C pf hr
      exact extra_unordered_ext D (Or.inl ⟨h₁.trans h₃.symm,h₂.trans h₄.symm⟩)
    · obtain ⟨h₁,h₂⟩ := pair_functional D C pe hq
      obtain ⟨h₃,h₄⟩ := pair_functional D C pf hr
      exact extra_unordered_ext D (Or.inr ⟨h₁.trans h₄.symm,h₂.trans h₃.symm⟩)
    · obtain ⟨h₁,h₂⟩ := pair_functional D C pe hq
      obtain ⟨h₃,h₄⟩ := pair_functional D C pf hr
      exact extra_unordered_ext D (Or.inr ⟨h₁.trans h₄.symm,h₂.trans h₃.symm⟩)
    · obtain ⟨h₁,h₂⟩ := pair_functional D C pe hq
      obtain ⟨h₃,h₄⟩ := pair_functional D C pf hr
      exact extra_unordered_ext D (Or.inl ⟨h₁.trans h₃.symm,h₂.trans h₄.symm⟩)
  subst f
  exact he.symm.trans hf

#print axioms selected_sound
#print axioms selected_coverage
#print axioms selected_unique
end StackSorting.GraphWidth.MarginalA2
