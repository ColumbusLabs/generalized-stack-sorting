import ArbitraryPrefixConnectivity

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

/-- On a fixed genuine prefix, every pair in the root bag has an actual
simple hyperpath avoiding the other root-adhesion vertices. The prefix is
preserved by pruning; this does not demand a second chosen prefix. -/
theorem exists_prefix_avoiding_route (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r : Fin n) (Z : Finset (Fin n)) (hZ : RelativePrefix O r Z)
    (s t : Fin n) (hs : RegionBag G O r s) (ht : RegionBag G O r t) :
    ∃ p : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t,
      ∀ x ∈ p.walk.vertices, rootAllowed G O r s t x := by
  classical
  let G' := inducedGraph G (rootAllowed G O r s t)
  let O' := prunedOrder G O r s t
  have he' : ∀ {u v}, G'.Adj u v → O'.rel u v ∨ O'.rel v u :=
    normalized_eliminates G' O (fun h => helim h.1)
  have hc' : ∀ v u, Cone O' v u → GraphWidth.Walk G'.Adj (Cone O' v) v u :=
    normalized_cone_walks G' O
  have hZ' := (pruned_relativePrefix_iff G O cones r s t Z).mpr hZ
  have hs' : s ∈ regionBagSet G' O' r := (mem_regionBagSet G' O' r s).mpr
    ((pruned_regionBag_iff G O cones r s t (cone_refl O r)).mpr ⟨hs,Or.inr (Or.inl rfl)⟩)
  have ht' : t ∈ regionBagSet G' O' r := (mem_regionBagSet G' O' r t).mpr
    ((pruned_regionBag_iff G O cones r s t (cone_refl O r)).mpr ⟨ht,Or.inr (Or.inr rfl)⟩)
  obtain ⟨ws⟩ := arbitrary_prefix_connected G' O' he' hc' r Z hZ' s
    (exposed_bag_subset G' O' r Z hZ' hZ'.2.1 hs')
  obtain ⟨wt⟩ := arbitrary_prefix_connected G' O' he' hc' r Z hZ' t
    (exposed_bag_subset G' O' r Z hZ' hZ'.2.1 ht')
  let w := (ws.append wt.reverse).mapEdges (canonicalActiveEdge G' O' r Z)
    (fun x e h => (canonicalActive_incidence G' O' r Z x e).mpr h)
  obtain ⟨p,_⟩ := w.exists_path
  let f := prunedActiveEdge G O cones r s t Z hZ
  let q := p.embedEdges f (prunedActiveEdge_injective G O cones r s t Z hZ)
    (prunedActiveEdge_incidence G O cones r s t Z hZ)
  refine ⟨q,?_⟩
  intro x hx
  have hx' : x ∈ p.walk.vertices := by
    simpa only [q,Path.embedEdges,HWalk.vertices_mapEdges] using hx
  apply p.walk.vertices_supported (rootAllowed G O r s t) ?_ (Or.inr (Or.inl rfl)) x hx'
  intro y e hy
  exact ((pruned_visible_iff G O cones r s t Z hZ y).mp
    (prefixHypertorso_support G' O' r Z hZ' y e.val hy.1)).2

end StackSorting.LowPathwidthParts
