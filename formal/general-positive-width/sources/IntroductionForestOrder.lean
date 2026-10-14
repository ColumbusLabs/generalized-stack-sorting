import DecompositionIntroduction
import Mathlib.Data.Finset.Card

namespace StackSorting.GraphWidth
open FinitePort

/-- Split each introduction-preorder class by the fixed original vertex order.
No relabeling of the vertices occurs in this relation. -/
def IntroductionEarlier {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (u v : Fin n) : Prop :=
  Ancestor T (introductionNode D u) (introductionNode D v) ∧
    (introductionNode D u ≠ introductionNode D v ∨ u.val < v.val)

theorem introductionEarlier_irrefl {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (v : Fin n) : ¬ IntroductionEarlier D v v := by
  simp [IntroductionEarlier]

theorem introductionEarlier_trans {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {u v w : Fin n}
    (huv : IntroductionEarlier D u v) (hvw : IntroductionEarlier D v w) :
    IntroductionEarlier D u w := by
  refine ⟨huv.1.trans hvw.1, ?_⟩
  by_cases huw : introductionNode D u = introductionNode D w
  · have hueq : introductionNode D u = introductionNode D v :=
      TreeAncestry.antisymm huv.1 (huw.symm ▸ hvw.1)
    have hveq : introductionNode D v = introductionNode D w := hueq.symm.trans huw
    have hu : u.val < v.val := huv.2.resolve_left (not_not.mpr hueq)
    have hv : v.val < w.val := hvw.2.resolve_left (not_not.mpr hveq)
    exact Or.inr (Nat.lt_trans hu hv)
  · exact Or.inl huw

/-- Strict ancestry raises this explicit finite numerical rank. -/
noncomputable def introductionRank {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (v : Fin n) : Nat :=
  (introductionNode D v).val * n + v.val

theorem introductionEarlier_rank_lt {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {u v : Fin n} (h : IntroductionEarlier D u v) :
    introductionRank D u < introductionRank D v := by
  by_cases he : introductionNode D u = introductionNode D v
  · have hl : u.val < v.val := h.2.resolve_left (not_not.mpr he)
    simp only [introductionRank, he]
    exact Nat.add_lt_add_left hl _
  · have hab := h.1.val_le
    have hne : (introductionNode D u).val ≠ (introductionNode D v).val :=
      fun eq => he (Fin.ext eq)
    have hstep : (introductionNode D u).val + 1 ≤ (introductionNode D v).val := by omega
    change (introductionNode D u).val*n+u.val < (introductionNode D v).val*n+v.val
    calc
      _ < (introductionNode D u).val*n+n := Nat.add_lt_add_left u.isLt _
      _ = ((introductionNode D u).val+1)*n := by simp [Nat.add_mul]
      _ ≤ (introductionNode D v).val*n := Nat.mul_le_mul_right n hstep
      _ ≤ _ := Nat.le_add_right _ _

/-- Predecessors of one vertex are linearly ordered after splitting ties. -/
theorem introductionEarlier_predecessors {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {u v w : Fin n}
    (hu : IntroductionEarlier D u w) (hv : IntroductionEarlier D v w) :
    IntroductionEarlier D u v ∨ u = v ∨ IntroductionEarlier D v u := by
  have hc := TreeAncestry.comparable hu.1 hv.1
  by_cases he : introductionNode D u = introductionNode D v
  · rcases Nat.lt_trichotomy u.val v.val with h | h | h
    · exact Or.inl ⟨he ▸ Ancestor.refl _, Or.inr h⟩
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr ⟨he.symm ▸ Ancestor.refl _, Or.inr h⟩)
  · rcases hc with h | h
    · exact Or.inl ⟨h, Or.inl he⟩
    · exact Or.inr (Or.inr ⟨h, Or.inl (Ne.symm he)⟩)

/-- Every original graph edge has comparable endpoints in the new order. -/
theorem introductionEarlier_eliminates {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {u v : Fin n} (h : G.Adj u v) :
    IntroductionEarlier D u v ∨ IntroductionEarlier D v u := by
  have hc := edge_introductions_comparable D h
  by_cases he : introductionNode D u = introductionNode D v
  · have huv : u ≠ v := by intro e; subst v; exact G.loopless _ h
    rcases Nat.lt_or_gt_of_ne (fun eq => huv (Fin.ext eq)) with h | h
    · exact Or.inl ⟨he ▸ Ancestor.refl _, Or.inr h⟩
    · exact Or.inr ⟨he.symm ▸ Ancestor.refl _, Or.inr h⟩
  · rcases hc with h | h
    · exact Or.inl ⟨h, Or.inl he⟩
    · exact Or.inr ⟨h, Or.inl (Ne.symm he)⟩

def IntroductionFrontier {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (v u : Fin n) : Prop :=
  u = v ∨ IntroductionEarlier D u v ∧
    ∃ w, (v = w ∨ IntroductionEarlier D v w) ∧ G.Adj u w

theorem introductionFrontier_subset {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {v u : Fin n} (h : IntroductionFrontier D v u) :
    u ∈ D.bag (introductionNode D v) := by
  rcases h with rfl | ⟨huv,w,hvw,he⟩
  · exact (introduction_spec D _).1
  · apply frontier_mem_introduction_bag D huv.1 ?_ he
    rcases hvw with rfl | hvw
    · exact Ancestor.refl _
    · exact hvw.1

noncomputable def introductionFrontierSet {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (IntroductionFrontier D v)

theorem introductionFrontier_card_le {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (v : Fin n) :
    (introductionFrontierSet D v).card ≤ (D.bag (introductionNode D v)).length := by
  classical
  apply (Finset.card_le_card (t := (D.bag (introductionNode D v)).toFinset) ?_).trans
    (List.toFinset_card_le _)
  intro u hu
  exact List.mem_toFinset.mpr (introductionFrontier_subset D (Finset.mem_filter.mp hu).2)

theorem introductionFrontier_bound {n t} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) {b : Nat} (hb : D.BagBound b) (v : Fin n) :
    (introductionFrontierSet D v).card ≤ b :=
  (introductionFrontier_card_le D v).trans (hb _)

#print axioms introductionEarlier_trans
#print axioms introductionEarlier_eliminates
#print axioms introductionFrontier_bound
end StackSorting.GraphWidth
