import HypergraphPathEmbedding

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

/-- The exact pruned-prefix payload used by the indexed routing induction.
Its paths live in the original hypertorso and avoid all unwanted root-adhesion
vertices; its bags come from the genuinely pruned hypertorso. -/
structure PrunedPrefixWitness (G : Graph n) (O : RankedOrder n) (r s t : Fin n)
    (k : Nat) (Z : Finset (Fin n)) where
  isPrefix : RelativePrefix O r Z
  first : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t
  second : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t
  shared : ∀ e, e ∈ first.walk.edges → e ∈ second.walk.edges → IsOriginal e.val
  first_allowed : ∀ x ∈ first.walk.vertices, rootAllowed G O r s t x
  second_allowed : ∀ x ∈ second.walk.vertices, rootAllowed G O r s t x
  bags : BagPath
    (Finset.univ : Finset {x : Fin n // x ∈ prefixVertices
      (inducedGraph G (rootAllowed G O r s t)) (prunedOrder G O r s t) r Z}) (2*k+2)
  covers : bags.Covers (SupportedIncidence
    (inc := ActiveIncidence (CanonicalPrefixInc (inducedGraph G (rootAllowed G O r s t))
      (prunedOrder G O r s t) r Z))
    (↑(prefixVertices (inducedGraph G (rootAllowed G O r s t)) (prunedOrder G O r s t) r Z)))

/-- Construct the pruned pair payload from the frozen 5.2 theorem, without
assuming that normalization preserves prefixes or endpoint avoidance. -/
theorem exists_pruned_prefix_witness (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (r s t : Fin n) (hs : s ∈ regionBagSet G O r) (ht : t ∈ regionBagSet G O r) :
    ∃ Z, Nonempty (PrunedPrefixWitness G O r s t k Z) := by
  classical
  let G' := inducedGraph G (rootAllowed G O r s t)
  let O' := prunedOrder G O r s t
  have he' : ∀ {u v}, G'.Adj u v → O'.rel u v ∨ O'.rel v u :=
    normalized_eliminates G' O (fun h => helim h.1)
  have hc' : ∀ v u, Cone O' v u → GraphWidth.Walk G'.Adj (Cone O' v) v u :=
    normalized_cone_walks G' O
  have hs' : s ∈ regionBagSet G' O' r := (mem_regionBagSet G' O' r s).mpr
    ((pruned_regionBag_iff G O cones r s t (cone_refl O r)).mpr
      ⟨(mem_regionBagSet G O r s).mp hs,Or.inr (Or.inl rfl)⟩)
  have ht' : t ∈ regionBagSet G' O' r := (mem_regionBagSet G' O' r t).mpr
    ((pruned_regionBag_iff G O cones r s t (cone_refl O r)).mpr
      ⟨(mem_regionBagSet G O r t).mp ht,Or.inr (Or.inr rfl)⟩)
  obtain ⟨Z,hZ',⟨p,q,hpq⟩,D,hD⟩ := exists_canonical_prefix_separation G' O' he' hc'
    k (pruned_width G O r s t k width) r s t hs' ht'
  have hZ := (pruned_relativePrefix_iff G O cones r s t Z).mp hZ'
  let f := prunedActiveEdge G O cones r s t Z hZ
  have inj := prunedActiveEdge_injective G O cones r s t Z hZ
  have forward := prunedActiveEdge_incidence G O cones r s t Z hZ
  let a := p.embedEdges f inj forward
  let b := q.embedEdges f inj forward
  have support : ∀ x e, ActiveIncidence (CanonicalPrefixInc G' O' r Z) x e → rootAllowed G O r s t x := by
    intro x e hx
    exact ((pruned_visible_iff G O cones r s t Z hZ x).mp
      (prefixHypertorso_support G' O' r Z hZ' x e.val hx.1)).2
  have ha : ∀ x ∈ a.walk.vertices, rootAllowed G O r s t x := by
    intro x hx
    have hx' : x ∈ p.walk.vertices := by simpa only [a,Path.embedEdges,HWalk.vertices_mapEdges] using hx
    exact p.walk.vertices_supported _ support (Or.inr (Or.inl rfl)) x hx'
  have hb : ∀ x ∈ b.walk.vertices, rootAllowed G O r s t x := by
    intro x hx
    have hx' : x ∈ q.walk.vertices := by simpa only [b,Path.embedEdges,HWalk.vertices_mapEdges] using hx
    exact q.walk.vertices_supported _ support (Or.inr (Or.inl rfl)) x hx'
  refine ⟨Z,⟨⟨hZ,a,b,?_,ha,hb,D,hD⟩⟩⟩
  intro e he hf
  have he' : e ∈ p.walk.edges.map f := by simpa only [a,Path.embedEdges,HWalk.edges_mapEdges] using he
  have hf' : e ∈ q.walk.edges.map f := by simpa only [b,Path.embedEdges,HWalk.edges_mapEdges] using hf
  obtain ⟨u,hu,hue⟩ := List.mem_map.mp he'
  obtain ⟨v,hv,hve⟩ := List.mem_map.mp hf'
  have huv := inj (hue.trans hve.symm)
  have horig := hpq u hu (huv.symm ▸ hv)
  exact congrArg Subtype.val hue ▸ horig

end StackSorting.LowPathwidthParts
