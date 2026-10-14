import SparseEliminationSyntax
import EliminationForestFromDecomposition

namespace StackSorting.SparseEndpointMSO.EliminationSyntax
open _root_.StackSorting.SparseEndpointMSO.CanonicalChoice GraphWidth FinitePort

/-- This is the precise, still external definable-introduction-preorder input.
It is a formula/semantic representation of a supplied actual decomposition,
not the desired forest or width conclusion. -/
def RepresentsIntroduction {n t k} {G : Graph n} {T : RootedTree t}
    (bags : Decomposition G T) (M : Model) (rho : Formula 2 k)
    (X : Fin k → Nat → Prop) : Prop :=
  ∀ u v : Fin n, RelationEval M rho X u.val v.val ↔
    Ancestor T (introductionNode bags u) (introductionNode bags v)

theorem splitPreorder_identifies {n t k} {G : Graph n} {T : RootedTree t}
    (bags : Decomposition G T) (M : Model) (hp : TimePath M n)
    (rho : Formula 2 k) (X : Fin k → Nat → Prop)
    (hr : RepresentsIntroduction bags M rho X) (u v : Fin n) :
    RelationEval M (splitPreorder rho) X u.val v.val ↔ IntroductionEarlier bags u v := by
  rw [eval_splitPreorder, hr u v, hr v u]
  have hu : u.val ∈ M.domain := by rw [hp.1]; exact List.mem_range.mpr u.isLt
  have hv : v.val ∈ M.domain := by rw [hp.1]; exact List.mem_range.mpr v.isLt
  have hc : OrderEval M chronologicalBefore u.val v.val ↔ u.val < v.val :=
    eval_strictBefore M n hp 0 1 (pairEnv u.val v.val) Fin.elim0 hu hv
  rw [hc]
  apply and_congr_right
  intro h
  apply or_congr ?_ Iff.rfl
  constructor
  · intro hn he
    exact hn (he ▸ Ancestor.refl _)
  · intro hn hrev
    exact hn (TreeAncestry.antisymm h hrev)

theorem coverFormula_identifies {n t k} {G : Graph n} {T : RootedTree t}
    (bags : Decomposition G T) (M : Model) (hp : TimePath M n)
    (rho : Formula 2 k) (X : Fin k → Nat → Prop)
    (hr : RepresentsIntroduction bags M rho X) (u v : Fin n) :
    RelationEval M (coverFormula (splitPreorder rho)) X u.val v.val ↔
      (introductionOrder bags).Cover u v := by
  rw [eval_coverFormula, splitPreorder_identifies bags M hp rho X hr u v]
  apply and_congr_right
  intro _
  apply not_congr
  constructor
  · rintro ⟨z,hz,huz,hzv⟩
    have hb : z < n := by simpa only [hp.1, List.mem_range] using hz
    let w : Fin n := ⟨z,hb⟩
    exact ⟨w,(splitPreorder_identifies bags M hp rho X hr u w).mp huz,
      (splitPreorder_identifies bags M hp rho X hr w v).mp hzv⟩
  · rintro ⟨w,huw,hwv⟩
    refine ⟨w.val, ?_, (splitPreorder_identifies bags M hp rho X hr u w).mpr huw,
      (splitPreorder_identifies bags M hp rho X hr w v).mpr hwv⟩
    rw [hp.1]
    exact List.mem_range.mpr w.isLt

/-- The explicit sparse formula names exactly the nonroot links of the
constructed actual same-vertex parent forest. -/
theorem parentFormula_exact {n t k} {G : Graph n} {T : RootedTree t}
    (bags : Decomposition G T) (M : Model) (hp : TimePath M n)
    (rho : Formula 2 k) (X : Fin k → Nat → Prop)
    (hr : RepresentsIntroduction bags M rho X) (u v : Fin n) :
    RelationEval M (coverFormula (splitPreorder rho)) X u.val v.val ↔
      (eliminationForest bags).parent v = u ∧ u ≠ v := by
  rw [coverFormula_identifies bags M hp rho X hr]
  constructor
  · intro h
    have hn : u ≠ v := by
      intro e
      subst u
      exact introductionEarlier_irrefl bags v h.1
    exact ⟨((introductionOrder bags).parent_eq_iff_cover hn).mpr h, hn⟩
  · rintro ⟨he,hn⟩
    exact ((introductionOrder bags).parent_eq_iff_cover hn).mp he

#print axioms splitPreorder_identifies
#print axioms coverFormula_identifies
#print axioms parentFormula_exact
end StackSorting.SparseEndpointMSO.EliminationSyntax
