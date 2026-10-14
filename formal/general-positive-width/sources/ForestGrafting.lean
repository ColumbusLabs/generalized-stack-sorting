import ForestDisjointUnion
import WalkOnePointBoundary

namespace StackSorting.GuidedPathwidth
universe u
variable {J N : Type u}

/-- Candidate graph for grafting every old forest fiber to its named spine
node. Each candidate attachment is an actual edge between these two nodes. -/
def graftGraph (T : SimpleGraph J) (U : SimpleGraph N) (f : N → J) :
    SimpleGraph (J ⊕ N) where
  Adj a b := match a,b with
    | .inl j,.inl k => T.Adj j k
    | .inr x,.inr y => U.Adj x y
    | .inl j,.inr x => f x = j
    | .inr x,.inl j => f x = j
  symm := ⟨by intro a b h; cases a <;> cases b <;> simp_all [SimpleGraph.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

def graftFiber (f : N → J) (j : J) : Set (J ⊕ N) :=
  {a | match a with | .inl k => k = j | .inr x => f x = j}

structure GraftedForest (T : SimpleGraph J) (U : SimpleGraph N) (f : N → J) where
  graph : SimpleGraph (J ⊕ N)
  acyclic : graph.IsAcyclic
  oldEdges : T ⊕g U ≤ graph
  allowedEdges : graph ≤ graftGraph T U f
  fiberConnected : ∀ a, ReachIn graph (graftFiber f (f a)) (.inr a) (.inl (f a))

/-- The graft is an actual acyclic graph retaining every old spine and child
edge. Its root paths stay inside their named column fiber. -/
theorem exists_graftedForest {T : SimpleGraph J} {U : SimpleGraph N} {f : N → J}
    (hT : T.IsAcyclic) (hU : U.IsAcyclic)
    (hf : ∀ {a b}, U.Adj a b → f a = f b) : Nonempty (GraftedForest T U f) := by
  have hle : T ⊕g U ≤ graftGraph T U f := by
    intro a b h
    cases a <;> cases b <;> simp_all [graftGraph]
  obtain ⟨F,hOld,hNew,hA,hReach⟩ :=
    (graftGraph T U f).exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
      hle (sumForest_acyclic hT hU)
  refine ⟨⟨F,hA,hOld,hNew,?_⟩⟩
  intro a
  apply reachIn_of_onePointBoundary (show Sum.inr a ∈ graftFiber f (f a) from rfl)
    (show Sum.inl (f a) ∈ graftFiber f (f a) from rfl)
  · intro x y hx hxr hxy
    have h := hNew hxy
    cases x with
    | inl j =>
      have hj : j = f a := hx
      exact (hxr (congrArg Sum.inl hj)).elim
    | inr b =>
      cases y with
      | inl j =>
        change j = f a
        have hbj : f b = j := h
        exact hbj.symm.trans hx
      | inr c =>
        change f c = f a
        exact (hf h).symm.trans hx
  · rw [hReach]
    exact (show (graftGraph T U f).Adj (.inr a) (.inl (f a)) from rfl).reachable

#print axioms exists_graftedForest
end StackSorting.GuidedPathwidth
