import NormalizedPrefixReplacement

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization FiniteFlow.Hypergraph
variable {n : Nat}

theorem singleton_prefix_vertices (G : Graph n) (O : RankedOrder n) (r : Fin n) :
    prefixVertices G O r {r} = regionBagSet G O r := by
  classical
  rw [prefixVertices_eq_bag_union G O r {r} (relativePrefix_singleton O r)]
  simp

/-- Each local root-bag connection is an actual edge of the singleton prefix. -/
theorem root_local_incidence (G : Graph n) (O : RankedOrder n) (r x : Fin n)
    (e : (Fin n × Fin n) ⊕ Fin n) (h : LocalHypertorsoInc G O r x e) :
    PrefixHypertorsoInc G O r {r} x e := by
  classical
  cases e with
  | inl e =>
    refine ⟨h.1,?_,?_,h.2.2.2.2⟩
    · rw [singleton_prefix_vertices]
      exact (mem_regionBagSet G O r e.1).mpr h.2.2.1
    · rw [singleton_prefix_vertices]
      exact (mem_regionBagSet G O r e.2).mpr h.2.2.2.1
  | inr c =>
    have hcr : c ≠ r := fun he => h.2.1 (h.1.trans he.symm)
    refine ⟨⟨by simpa using hcr,?_⟩,h.2.2⟩
    simp only [clippedParent,ite_eq_right hcr,h.1,Finset.mem_singleton]

/-- Base connectivity uses the actual root bag, even when the ambient graph
contains unexposed vertices. -/
theorem singleton_prefix_connected (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (r x y : Fin n) (hx : x ∈ prefixVertices G O r {r})
    (hy : y ∈ prefixVertices G O r {r}) :
    Nonempty (HWalk (ActiveIncidence (PrefixHypertorsoInc G O r {r})) x y) := by
  rw [singleton_prefix_vertices] at hx hy
  obtain ⟨w⟩ := localHypertorso_connected G O helim cones r x y hx hy
  exact ⟨(w.mapEdges (inc := LocalHypertorsoInc G O r)
    (inc' := PrefixHypertorsoInc G O r {r}) id
    (fun x e h => root_local_incidence G O r x e h)).activate⟩

theorem singleton_prefix_thin (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u)
    (r : Fin n) (k : Nat) (width : (regionBagSet G O r).card ≤ k+1)
    (s t : Fin n) (hs : s ∈ prefixVertices G O r {r}) (ht : t ∈ prefixVertices G O r {r}) :
    ∃ p : Path (ActiveIncidence (PrefixHypertorsoInc G O r {r})) s t,
      ThinNetworkLocalWitnesses p k := by
  classical
  obtain ⟨w⟩ := singleton_prefix_connected G O helim cones r s t hs ht
  obtain ⟨p,_⟩ := w.exists_path
  refine ⟨p,small_supported_network_is_thin (prefixVertices G O r {r}) k ?_ ?_ hs ht p⟩
  · simpa only [singleton_prefix_vertices] using width
  · intro x e hx
    exact prefixHypertorso_support G O r {r} (relativePrefix_singleton O r) x e.val hx

end StackSorting.PrefixGrowth
