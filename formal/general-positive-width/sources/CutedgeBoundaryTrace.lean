import CutedgeClassification

namespace FiniteFlow.Hypergraph
variable {V E : Type*} {inc : V → E → Prop} {s t : V}

noncomputable def boundaryTrace (p : Path inc s t) : List (CutBoundary E) :=
  .source :: (cutedgeTrace p).map CutBoundary.cut ++ [.sink]

theorem mem_boundaryTrace (p : Path inc s t) (b : CutBoundary E) :
    b ∈ boundaryTrace p ↔ BoundaryValid (inc := inc) (s := s) (t := t) b := by
  cases b <;> simp [boundaryTrace,BoundaryValid]

theorem boundaryTrace_pairwise [DecidableEq E] (p : Path inc s t) :
    (boundaryTrace p).Pairwise (BoundaryBefore p) := by
  have hcuts : ((cutedgeTrace p).map CutBoundary.cut).Pairwise (BoundaryBefore p) := by
    simpa only [List.pairwise_map,BoundaryBefore] using cutedgeTrace_pairwise p
  apply List.pairwise_cons.mpr
  constructor
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
      trivial
    · have : b = .sink := by simpa only [List.mem_singleton] using hb
      subst b
      trivial
  · apply List.pairwise_append.mpr
    refine ⟨hcuts,by simp,?_⟩
    intro a ha b hb
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp ha
    have : b = .sink := by simpa only [List.mem_singleton] using hb
    subst b
    trivial

theorem boundaryBefore_irrefl [DecidableEq E] (p : Path inc s t) (a : CutBoundary E) :
    ¬ BoundaryBefore p a a := by cases a <;> simp [BoundaryBefore]

theorem boundaryTrace_nodup [DecidableEq E] (p : Path inc s t) :
    (boundaryTrace p).Nodup :=
  (boundaryTrace_pairwise p).imp (fun h he => by subst_vars; exact boundaryBefore_irrefl p _ h)

/-- The abstract boundary order from the accepted classification is precisely
the concrete list order, now made available for bag-chain indexing. -/
theorem boundaryTrace_get_before [DecidableEq E] (p : Path inc s t)
    (i j : Fin (boundaryTrace p).length) :
    BoundaryBefore p ((boundaryTrace p).get i) ((boundaryTrace p).get j) ↔ i < j := by
  constructor
  · intro h
    by_contra hn
    have hji : j ≤ i := Nat.le_of_not_gt hn
    rcases lt_or_eq_of_le hji with hlt | heq
    · have hrev := (List.pairwise_iff_getElem.mp (boundaryTrace_pairwise p))
        j.val i.val j.isLt i.isLt hlt
      change BoundaryBefore p ((boundaryTrace p).get j) ((boundaryTrace p).get i) at hrev
      cases hi : (boundaryTrace p).get i <;> cases hj : (boundaryTrace p).get j <;>
        simp only [hi,hj,BoundaryBefore] at h hrev
      exact Nat.lt_asymm h hrev
    · have hij : i = j := heq.symm
      subst j
      exact boundaryBefore_irrefl p _ h
  · intro h
    exact (List.pairwise_iff_getElem.mp (boundaryTrace_pairwise p))
      i.val j.val i.isLt j.isLt h

end FiniteFlow.Hypergraph
