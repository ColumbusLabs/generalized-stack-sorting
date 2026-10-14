import PrunedPrefixGeometry

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}
attribute [local instance] Classical.propDecidable

theorem pruned_visible_iff (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (x : Fin n) :
    x ∈ prefixVertices (inducedGraph G (rootAllowed G O r s t)) (prunedOrder G O r s t) r Z ↔
      x ∈ prefixVertices G O r Z ∧ rootAllowed G O r s t x := by
  simp only [prefixVertices,Finset.mem_union,mem_regionAdhesionSet,
    pruned_adhesion_iff G O cones r s t (cone_refl O r)]
  constructor
  · rintro (hx | ⟨hx,hkeep⟩)
    · exact ⟨Or.inl hx,cone_allowed G O r s t (hp.2.2 x hx)⟩
    · exact ⟨Or.inr hx,hkeep⟩
  · rintro ⟨hx,hkeep⟩
    exact hx.elim Or.inl (fun h => Or.inr ⟨h,hkeep⟩)

theorem pruned_prefix_incidence_old (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (x : Fin n) (e : (Fin n × Fin n) ⊕ Fin n)
    (h : PrefixHypertorsoInc (inducedGraph G (rootAllowed G O r s t))
      (prunedOrder G O r s t) r Z x e) : PrefixHypertorsoInc G O r Z x e := by
  cases e with
  | inl e =>
    exact ⟨h.1.1,((pruned_visible_iff G O cones r s t Z hp e.1).mp h.2.1).1,
      ((pruned_visible_iff G O cones r s t Z hp e.2).mp h.2.2.1).1,h.2.2.2⟩
  | inr z =>
    have hz := (pruned_frontier_iff G O cones r s t Z hp z).mp h.1
    have hzr : Cone O r z := Or.inl (relative_frontier_cone O r Z hp z hz).1
    exact ⟨hz,((pruned_adhesion_iff G O cones r s t hzr).mp h.2).1⟩

noncomputable def prunedActiveEdge (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (e : ActiveEdge (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
      (prunedOrder G O r s t) r Z)) : ActiveEdge (CanonicalPrefixInc G O r Z) :=
  ⟨e.val,by
    obtain ⟨x,hx⟩ := e.property
    exact ⟨x,pruned_prefix_incidence_old G O cones r s t Z hp x e.val hx.1,hx.2⟩⟩

theorem prunedActiveEdge_injective (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) :
    Function.Injective (prunedActiveEdge G O cones r s t Z hp) := by
  intro e d h
  have he := congrArg (fun z : ActiveEdge (CanonicalPrefixInc G O r Z) => z.val) h
  exact Subtype.ext he

theorem prunedActiveEdge_incidence (G : Graph n) (O : RankedOrder n)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r s t : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (x : Fin n) (e : ActiveEdge (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
      (prunedOrder G O r s t) r Z))
    (h : ActiveIncidence (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
      (prunedOrder G O r s t) r Z) x e) :
    ActiveIncidence (CanonicalPrefixInc G O r Z) x (prunedActiveEdge G O cones r s t Z hp e) :=
  ⟨pruned_prefix_incidence_old G O cones r s t Z hp x e.val h.1,h.2⟩

end StackSorting.LowPathwidthParts
