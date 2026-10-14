import DecompositionForests
import Mathlib.Combinatorics.SimpleGraph.Sum

namespace StackSorting.GuidedPathwidth
universe u v
variable {N : Type u} {M : Type v}

/-- A walk in a graph sum cannot cross between its two actual summands. -/
theorem sumWalk_side {T : SimpleGraph N} {U : SimpleGraph M} {x y : N ⊕ M}
    (p : (T ⊕g U).Walk x y) {z : N ⊕ M} (hz : z ∈ p.support) :
    z.isLeft = x.isLeft := by
  revert hz
  induction p with
  | @nil x =>
    intro hz
    have he : z = x := by simpa using hz
    exact congrArg Sum.isLeft he
  | @cons x y w hxy p ih =>
    intro hz
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
    rcases hz with rfl | hz
    · rfl
    · have he : y.isLeft = x.isLeft := by
        cases x <;> cases y <;> simp_all
      exact (ih hz).trans he

/-- Actual disjoint union preserves acyclicity. -/
theorem sumForest_acyclic {T : SimpleGraph N} {U : SimpleGraph M}
    (hT : T.IsAcyclic) (hU : U.IsAcyclic) : (T ⊕g U).IsAcyclic := by
  intro x p hp
  let S : Set (N ⊕ M) := {y | y.isLeft = x.isLeft}
  have hs : ∀ z ∈ p.support, z ∈ S := fun z hz => sumWalk_side p hz
  let q := p.induce S hs
  have hq : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map
      (f := (SimpleGraph.Embedding.induce (G := T ⊕g U) S).toHom)
    simpa [q] using hp
  cases x with
  | inl a =>
    let f : (T ⊕g U).induce S →g T := {
      toFun := fun y => Sum.elim id (fun _ => a) y.val
      map_rel' := by
        rintro ⟨b,hb⟩ ⟨c,hc⟩ h
        change b.isLeft = true at hb
        change c.isLeft = true at hc
        cases b <;> cases c <;> simp_all
        all_goals cases hb }
    have hf : Function.Injective f := by
      rintro ⟨b,hb⟩ ⟨c,hc⟩ he
      change b.isLeft = true at hb
      change c.isLeft = true at hc
      change Sum.elim id (fun _ => a) b = Sum.elim id (fun _ => a) c at he
      apply Subtype.ext
      cases b <;> cases c <;> simp_all
      all_goals cases hb <;> cases hc
    exact hT (q.map f) (hq.map hf)
  | inr a =>
    let f : (T ⊕g U).induce S →g U := {
      toFun := fun y => Sum.elim (fun _ => a) id y.val
      map_rel' := by
        rintro ⟨b,hb⟩ ⟨c,hc⟩ h
        change b.isLeft = false at hb
        change c.isLeft = false at hc
        cases b <;> cases c <;> simp_all
        all_goals cases hb }
    have hf : Function.Injective f := by
      rintro ⟨b,hb⟩ ⟨c,hc⟩ he
      change b.isLeft = false at hb
      change c.isLeft = false at hc
      change Sum.elim (fun _ => a) id b = Sum.elim (fun _ => a) id c at he
      apply Subtype.ext
      cases b <;> cases c <;> simp_all
      all_goals cases hb <;> cases hc
    exact hU (q.map f) (hq.map hf)
end StackSorting.GuidedPathwidth
