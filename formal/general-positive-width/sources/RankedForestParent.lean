import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Lemmas

namespace StackSorting.SameVertexForest

/-- An explicitly ranked strict forest order. Lower cones are chains; no
parent, ancestry or uniqueness is supplied in this input structure. -/
structure RankedOrder (n : Nat) where
  rel : Fin n → Fin n → Prop
  irrefl : ∀ v, ¬ rel v v
  trans : ∀ {u v w}, rel u v → rel v w → rel u w
  predecessors : ∀ {u v w}, rel u w → rel v w → rel u v ∨ u = v ∨ rel v u
  rank : Fin n → Nat
  increasing : ∀ {u v}, rel u v → rank u < rank v

namespace RankedOrder
variable {n : Nat} (O : RankedOrder n)

noncomputable def maximalPredecessor (v : Fin n) (h : ∃ u, O.rel u v) : Fin n := by
  classical
  exact Classical.choose (Set.exists_max_image {u | O.rel u v} O.rank (Set.toFinite _) h)

theorem maximalPredecessor_spec (v : Fin n) (h : ∃ u, O.rel u v) :
    O.rel (O.maximalPredecessor v h) v ∧
      ∀ u, O.rel u v → O.rank u ≤ O.rank (O.maximalPredecessor v h) := by
  classical
  exact Classical.choose_spec (Set.exists_max_image {u | O.rel u v} O.rank (Set.toFinite _) h)

/-- A root is its own parent; otherwise choose the unique immediate predecessor. -/
noncomputable def parent (v : Fin n) : Fin n := by
  classical
  exact if h : ∃ u, O.rel u v then O.maximalPredecessor v h else v

theorem parent_of_pred {u v : Fin n} (h : O.rel u v) :
    O.rel (O.parent v) v ∧ ∀ w, O.rel w v → O.rank w ≤ O.rank (O.parent v) := by
  classical
  have hex : ∃ u, O.rel u v := ⟨u,h⟩
  simp only [parent, dite_eq_left hex]
  exact O.maximalPredecessor_spec v hex

theorem parent_ne_of_pred {u v : Fin n} (h : O.rel u v) : O.parent v ≠ v := by
  intro he
  exact O.irrefl v (by simpa only [he] using (O.parent_of_pred h).1)

theorem parent_rel {v : Fin n} (h : O.parent v ≠ v) : O.rel (O.parent v) v := by
  classical
  by_cases he : ∃ u, O.rel u v
  · obtain ⟨u,hu⟩ := he; exact (O.parent_of_pred hu).1
  · exact False.elim (h (by simp [parent, he]))

theorem parent_rank_lt {v : Fin n} (h : O.parent v ≠ v) :
    O.rank (O.parent v) < O.rank v := O.increasing (O.parent_rel h)

def Cover (u v : Fin n) : Prop :=
  O.rel u v ∧ ¬ ∃ w, O.rel u w ∧ O.rel w v

theorem parent_cover {u v : Fin n} (h : O.rel u v) : O.Cover (O.parent v) v := by
  refine ⟨(O.parent_of_pred h).1, ?_⟩
  rintro ⟨w, hpw, hwv⟩
  exact Nat.not_lt_of_ge ((O.parent_of_pred h).2 w hwv) (O.increasing hpw)

theorem cover_unique {u v w : Fin n} (hu : O.Cover u w) (hv : O.Cover v w) : u = v := by
  rcases O.predecessors hu.1 hv.1 with h | h | h
  · exact False.elim (hu.2 ⟨v,h,hv.1⟩)
  · exact h
  · exact False.elim (hv.2 ⟨u,h,hu.1⟩)

theorem parent_eq_iff_cover {u v : Fin n} (h : u ≠ v) :
    O.parent v = u ↔ O.Cover u v := by
  constructor
  · intro he
    have hne : O.parent v ≠ v := fun hp => h (he.symm.trans hp)
    have hc := O.parent_cover (O.parent_rel hne)
    exact he ▸ hc
  · intro hc
    exact O.cover_unique (O.parent_cover hc.1) hc

end RankedOrder

/-- A finite parent forest directly on the original vertices. Numeric labels
need not be a topological numbering; the decreasing rank excludes cycles. -/
structure Forest (n : Nat) where
  parent : Fin n → Fin n
  rank : Fin n → Nat
  decreasing : ∀ v, parent v ≠ v → rank (parent v) < rank v

inductive Ancestor {n : Nat} (F : Forest n) : Fin n → Fin n → Prop
  | refl (v) : Ancestor F v v
  | step {u v} : F.parent v ≠ v → Ancestor F u (F.parent v) → Ancestor F u v

noncomputable def RankedOrder.forest {n : Nat} (O : RankedOrder n) : Forest n where
  parent := O.parent
  rank := O.rank
  decreasing _ h := O.parent_rank_lt h

namespace RankedOrder
variable {n : Nat} (O : RankedOrder n)

theorem rel_of_ancestor {u v : Fin n} (h : Ancestor O.forest u v) : O.rel u v ∨ u = v := by
  induction h with
  | refl => exact Or.inr rfl
  | @step v hv hp ih =>
    have hpar : O.rel (O.parent v) v := O.parent_rel hv
    rcases ih with hu | he
    · exact Or.inl (O.trans hu hpar)
    · exact Or.inl (he.symm ▸ hpar)

/-- Every order ancestor is reached by the constructed immediate-parent links. -/
theorem ancestor_of_rel (O : RankedOrder n) {u v : Fin n} (h : O.rel u v) : Ancestor O.forest u v := by
  have hp := (O.parent_of_pred h).1
  have hn := O.parent_ne_of_pred h
  apply Ancestor.step hn
  rcases O.predecessors h hp with hu | he | hu
  · exact ancestor_of_rel O hu
  · subst u; exact Ancestor.refl _
  · exact False.elim (Nat.not_lt_of_ge ((O.parent_of_pred h).2 u h) (O.increasing hu))
termination_by O.rank v
decreasing_by exact O.parent_rank_lt hn

theorem ancestor_iff {u v : Fin n} :
    Ancestor O.forest u v ↔ O.rel u v ∨ u = v := by
  constructor
  · exact O.rel_of_ancestor
  · rintro (h | rfl)
    · exact O.ancestor_of_rel h
    · exact Ancestor.refl _

#print axioms parent_eq_iff_cover
#print axioms ancestor_iff
end RankedOrder
end StackSorting.SameVertexForest
