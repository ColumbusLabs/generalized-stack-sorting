import NetworkThinCertificates

namespace FiniteFlow.Hypergraph
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {inc : V → E → Prop} {s t : V}

structure NetworkPieceData
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t)
    (k : Nat) (h : Fin (2*(boundaryTrace p).length-1)) where
  path : BagPath (homePart (networkHome connected p) (networkExtra p) h) (2*k+2)
  covers : path.Covers inc
  extra_bag : ∀ q, q ≤ path.last → networkExtra p h ⊆ path.bag q
  first : ∀ (j : Fin (2*(boundaryTrace p).length-1)) (x : V), j.val+1=h.val → networkHome connected p x=h →
    x ∈ networkExtra p j → x ∈ path.bag 0
  last : ∀ (j : Fin (2*(boundaryTrace p).length-1)) (x : V), h.val+1=j.val → networkHome connected p x=h →
    x ∈ networkExtra p j → x ∈ path.bag path.last

/-- Build every chain piece from local thinness certificates. Even pieces add
one whole separator to an appendix restriction. Odd pieces restrict the actual
bridge certificate. All endpoint seam conditions are proved here. -/
noncomputable def buildNetworkPiece
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (k : Nat)
    (T : ThinBagCertificates p k)
    (rank : ∀ i, (boundaryVertices p i).card ≤ k+1)
    (h : Fin (2*(boundaryTrace p).length-1)) : NetworkPieceData connected p k h := by
  classical
  have hlen := boundaryTrace_length_ge_two p
  by_cases heven : h.val % 2 = 0
  · let i : Fin (boundaryTrace p).length := ⟨h.val/2,by have := h.isLt; omega⟩
    have hpos : h.val=2*i.val := by dsimp [i]; omega
    have heq := networkExtra_even_eq p h i hpos
    have hsub : homeCore (networkHome connected p) h ⊆ oneBoundaryVertices p i := by
      intro x hx
      apply networkHome_even_region connected p x i
      rw [(mem_homeCore _ _ _).mp hx]
      exact hpos
    let C := (T.appendix i).restrictSubset (homeCore (networkHome connected p) h) hsub
    have small : (networkExtra p h).card ≤ k+1 := by rw [heq]; exact rank i
    let D := C.augmentThin k (networkExtra p h) small
    refine ⟨D,?_,?_,?_,?_⟩
    · exact C.augmentThin_covers k (networkExtra p h) small
        ((T.appendix i).restrictSubset_covers _ hsub (T.appendix_cover i))
    · intro q _
      exact Finset.subset_union_right
    · intro j x hj _ hx
      obtain ⟨a,ha,_⟩ := (mem_networkExtra p j x).mp hx
      omega
    · intro j x hj _ hx
      obtain ⟨a,ha,_⟩ := (mem_networkExtra p j x).mp hx
      omega
  · let i : Fin (boundaryTrace p).length := ⟨h.val/2,by have := h.isLt; omega⟩
    let j : Fin (boundaryTrace p).length := ⟨h.val/2+1,by have := h.isLt; omega⟩
    have hstep : i.val+1=j.val := rfl
    have hpos : h.val=2*i.val+1 := by dsimp [i]; omega
    have hempty := networkExtra_odd_empty p h i.val hpos
    have hsub : homePart (networkHome connected p) (networkExtra p) h ⊆ bridgeVertices p i j := by
      intro x hx
      have hxcore : x ∈ homeCore (networkHome connected p) h := by
        simpa only [homePart,hempty,Finset.union_empty] using hx
      apply networkHome_odd_region connected p x i j hstep
      rw [(mem_homeCore _ _ _).mp hxcore]
      exact hpos
    let C := T.bridge i j hstep
    let D := C.restrictSubset (homePart (networkHome connected p) (networkExtra p) h) hsub
    refine ⟨D,C.restrictSubset_covers _ hsub (T.bridge_cover i j hstep),?_,?_,?_⟩
    · intro q _
      rw [hempty]
      exact Finset.empty_subset _
    · intro a x ha hhome hx
      obtain ⟨b,hb,hxb⟩ := (mem_networkExtra p a x).mp hx
      have hbi : b = i := Fin.ext (by omega)
      have hxpart : x ∈ homePart (networkHome connected p) (networkExtra p) h :=
        Finset.mem_union_left _ ((mem_homeCore _ _ _).mpr hhome)
      change x ∈ C.bag 0 ∩ homePart (networkHome connected p) (networkExtra p) h
      refine Finset.mem_inter.mpr ⟨?_,hxpart⟩
      apply T.bridge_first i j hstep x (hsub hxpart)
      apply (mem_boundaryVertices p i x).mpr
      exact hbi ▸ hxb
    · intro a x ha hhome hx
      obtain ⟨b,hb,hxb⟩ := (mem_networkExtra p a x).mp hx
      have hbj : b = j := Fin.ext (by omega)
      have hxpart : x ∈ homePart (networkHome connected p) (networkExtra p) h :=
        Finset.mem_union_left _ ((mem_homeCore _ _ _).mpr hhome)
      change x ∈ C.bag C.last ∩ homePart (networkHome connected p) (networkExtra p) h
      refine Finset.mem_inter.mpr ⟨?_,hxpart⟩
      apply T.bridge_last i j hstep x (hsub hxpart)
      apply (mem_boundaryVertices p j x).mpr
      exact hbj ▸ hxb

/-- Global finite bag-path assembly for the actual cutedge component unions.
The cutedge-rank premise is explicit. Every global seam, running-intersection
law and full-hyperedge covering bag is constructed from local thinness data. -/
theorem thin_network_global_bag_assembly
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (k : Nat)
    (T : ThinBagCertificates p k)
    (rank : ∀ e, Cutedge inc s t e → (hyperedgeVertices inc e).card ≤ k+1) :
    ∃ D : BagPath (Finset.univ : Finset V) (2*k+2), D.Covers inc := by
  let pieces := buildNetworkPiece connected p k T (boundaryVertices_rank p k rank)
  have hn : 0 < 2*(boundaryTrace p).length-1 := by
    have := boundaryTrace_length_ge_two p
    omega
  exact radius_one_bag_assembly hn (networkHome connected p) (networkExtra p)
    (fun i => (pieces i).path) (networkExtra_radius connected p)
    (fun i => (pieces i).extra_bag)
    (fun i => (pieces i).first) (fun i => (pieces i).last)
    (fun i => (pieces i).covers) (networkHome_edge_cases connected p)

end FiniteFlow.Hypergraph
