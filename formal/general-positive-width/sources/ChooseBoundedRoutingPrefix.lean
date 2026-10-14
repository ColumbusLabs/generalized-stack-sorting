import BalancedPrefixRouting

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

/-- Construct the complete first stage of the residual-budget induction:
an actual prefix, all indexed initial hyperpaths, their cubic boundary cap,
and the genuine small-pathwidth payload for the root marginal. -/
theorem exists_bounded_routing_prefix (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1)
    (r : Fin n) (D : IncomingDemands G O r) (hcap : D.indices.card ≤ 2*k^3) :
    ∃ Z, RelativePrefix O r Z ∧ ∃ F : PrefixRoutingFamily G O r D Z,
      F.Bounded k ∧ (Z = {r} ∨ ∃ s t, Nonempty (PrunedPrefixWitness G O r s t k Z)) := by
  classical
  by_cases hI : D.indices = ∅
  · let Z : Finset (Fin n) := {r}
    have hp := relativePrefix_singleton O r
    let F := defaultPrefixRoutes G O helim cones r D Z hp
    refine ⟨Z,hp,F,?_,Or.inl rfl⟩
    intro z
    have hempty : F.pendingUses z = ∅ := by simp [PrefixRoutingFamily.pendingUses,hI]
    have hk : k ≤ 2*k^3 := by
      simpa using IndexedEndpointLoad.cubic_load_bound k 0 0 (by omega) (by omega)
    simpa only [hempty,Finset.card_empty,Nat.zero_add] using (F.freshUses_bound k width z).trans hk
  · let endpoints := fun i => (D.source i,D.target i)
    let adhesion := regionAdhesionSet G O r
    have hend : ∀ i ∈ D.indices, (endpoints i).1 ∈ adhesion ∧ (endpoints i).2 ∈ adhesion := by
      intro i hi
      exact ⟨(mem_regionAdhesionSet G O r _).mpr (D.endpoints i hi).1,
        (mem_regionAdhesionSet G O r _).mpr (D.endpoints i hi).2⟩
    obtain ⟨p,hp,_hmax,hcount⟩ := IndexedEndpointLoad.exists_largest_endpoint_fiber
      D.indices adhesion endpoints hend (Finset.nonempty_iff_ne_empty.mpr hI)
    let S := D.indices.filter (fun i => endpoints i = p)
    obtain ⟨L,R,hLS,hRS,hdis,_hunion,hL,_hR,hLR,_hRL⟩ :=
      IndexedEndpointLoad.exists_balanced_partition S
    have hSI : S ⊆ D.indices := Finset.filter_subset _ _
    have hA : adhesion.card ≤ k := regionAdhesion_card_le G O k width r
    have hfiber : D.indices.card ≤ k*k*S.card := hcount.trans
      (Nat.mul_le_mul_right S.card (Nat.mul_le_mul hA hA))
    have hs := (mem_regionAdhesionSet G O r p.1).mp (Finset.mem_product.mp hp).1
    have ht := (mem_regionAdhesionSet G O r p.2).mp (Finset.mem_product.mp hp).2
    obtain ⟨Z,⟨W⟩⟩ := exists_pruned_prefix_witness G O helim cones k width r p.1 p.2
      ((mem_regionBagSet G O r p.1).mpr hs.2.1) ((mem_regionBagSet G O r p.2).mpr ht.2.1)
    let F := defaultPrefixRoutes G O helim cones r D Z W.isPrefix
    have ends : ∀ i ∈ L ∪ R, D.source i = p.1 ∧ D.target i = p.2 := by
      intro i hi
      have hiS : i ∈ S := (Finset.mem_union.mp hi).elim (fun h => hLS h) (fun h => hRS h)
      have he := (Finset.mem_filter.mp hiS).2
      exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
    let F' := F.withSplit p.1 p.2 W.first W.second W.first_allowed W.second_allowed L R ends
    refine ⟨Z,W.isPrefix,F',?_,Or.inr ⟨p.1,p.2,⟨W⟩⟩⟩
    exact F.withSplit_bounded p.1 p.2 W.first W.second W.first_allowed W.second_allowed W.shared
      S L R ends hSI hLS hRS hdis hL (by omega) k width hcap hfiber

end StackSorting.LowPathwidthParts
