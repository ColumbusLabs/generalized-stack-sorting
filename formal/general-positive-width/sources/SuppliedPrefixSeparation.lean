import CanonicalOriginalEdges

namespace StackSorting.PrefixGrowth
open GraphWidth SameVertexForest ConnectedConeNormalization
variable {n : Nat}

theorem normalized_region_bag_eq {t} {G : Graph n} {T : FinitePort.RootedTree t}
    (D : Decomposition G T) (v : Fin n) :
    regionBagSet G (normalizeSupplied D).order v = (normalizeSupplied D).bag v := by
  classical
  ext u
  simp only [mem_regionBagSet,normalizeSupplied,normalizedDecomposition,
    eliminationFrontierSet,Finset.mem_filter,Finset.mem_univ,true_and,regionBag_iff_frontier]

theorem normalized_cone_walks (G : Graph n) (O : RankedOrder n) (v u : Fin n)
    (hu : Cone (normalizedOrder G O) v u) :
    Walk G.Adj (Cone (normalizedOrder G O) v) v u := by
  exact (reachCone_connected G O (reachCone_refl G O v) ((normalized_cone G O v u).mp hu)).mono
    (fun x hx => (normalized_cone G O v x).mpr hx)

/-- Width-preserving normalization supplies the entire concrete prefix-separation
construction for each root of the normalized decomposition. The input is an
actual tree decomposition with bag bound k+1, with no pathwidth premise. -/
theorem supplied_normalized_prefix_separation {t} {G : Graph n} {T : FinitePort.RootedTree t}
    (D : Decomposition G T) (k : Nat) (width : D.BagBound (k+1))
    (r s u : Fin n) (hs : s ∈ (normalizeSupplied D).bag r)
    (hu : u ∈ (normalizeSupplied D).bag r) :
    ∃ Z : Finset (Fin n), RelativePrefix (normalizeSupplied D).order r Z ∧
      (∃ p q : FiniteFlow.Hypergraph.Path
        (FiniteFlow.Hypergraph.ActiveIncidence (CanonicalPrefixInc G (normalizeSupplied D).order r Z)) s u,
        ∀ e, e ∈ p.walk.edges → e ∈ q.walk.edges → IsOriginal e.val) ∧
      ∃ B : FiniteFlow.Hypergraph.BagPath
        (Finset.univ : Finset {x : Fin n // x ∈ prefixVertices G (normalizeSupplied D).order r Z}) (2*k+2),
        B.Covers (FiniteFlow.Hypergraph.SupportedIncidence
          (inc := FiniteFlow.Hypergraph.ActiveIncidence (CanonicalPrefixInc G (normalizeSupplied D).order r Z))
          (↑(prefixVertices G (normalizeSupplied D).order r Z))) := by
  apply exists_canonical_prefix_separation G (normalizeSupplied D).order
    (normalized_eliminates G (introductionOrder D) (introductionEarlier_eliminates D))
    (normalized_cone_walks G (introductionOrder D)) k
  · intro z
    rw [normalized_region_bag_eq]
    exact normalizeSupplied_bound D width z
  · simpa only [normalized_region_bag_eq] using hs
  · simpa only [normalized_region_bag_eq] using hu

end StackSorting.PrefixGrowth
