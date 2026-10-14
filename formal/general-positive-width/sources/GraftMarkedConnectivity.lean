import ForestGrafting

namespace StackSorting.GuidedPathwidth
universe u
variable {J N : Type u} {T : SimpleGraph J} {U : SimpleGraph N} {f : N → J}

namespace ReachIn
theorem reachable {V : Type u} {G : SimpleGraph V} {S : Set V} {x y : V}
    (h : ReachIn G S x y) : G.Reachable x y := by
  obtain ⟨p⟩ := h.induced
  exact ⟨p.map (SimpleGraph.Embedding.induce (G := G) S).toHom⟩
end ReachIn

def graftMarked (f : N → J) (j : J) (M : Set N) : Set (J ⊕ N) :=
  {a | match a with | .inl k => k = j | .inr x => f x = j ∧ x ∈ M}

/-- Any child-node predicate constant along old edges remains connected to
its column root using only marked nodes of that column. -/
theorem GraftedForest.markedConnected (F : GraftedForest T U f)
    (hf : ∀ {a b}, U.Adj a b → f a = f b) {M : Set N}
    (hM : ∀ {a b}, U.Adj a b → a ∈ M → b ∈ M) {a : N} (ha : a ∈ M) :
    ReachIn F.graph (graftMarked f (f a) M) (.inr a) (.inl (f a)) := by
  apply reachIn_of_onePointBoundary (show Sum.inr a ∈ graftMarked f (f a) M from ⟨rfl,ha⟩)
    (show Sum.inl (f a) ∈ graftMarked f (f a) M from rfl)
  · intro x y hx hxr hxy
    have h := F.allowedEdges hxy
    cases x with
    | inl j =>
      have hj : j = f a := hx
      exact (hxr (congrArg Sum.inl hj)).elim
    | inr b =>
      cases y with
      | inl j =>
        have hbj : f b = j := h
        exact hbj.symm.trans hx.1
      | inr c => exact ⟨(hf h).symm.trans hx.1,hM h hx.2⟩
  · exact (F.fiberConnected a).reachable
end StackSorting.GuidedPathwidth
