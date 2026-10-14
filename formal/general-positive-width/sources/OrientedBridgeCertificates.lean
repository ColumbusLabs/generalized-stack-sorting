import ReplacementBoundaryNeighbors

namespace FiniteFlow.Hypergraph
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {inc : V → E → Prop} {s t : V}

omit [DecidableEq V] [DecidableEq E] in
theorem bridgeVertices_swap (p : Path inc s t) (i j : Fin (boundaryTrace p).length) :
    bridgeVertices p i j = bridgeVertices p j i := by
  classical
  ext x
  simp only [mem_bridgeVertices, BridgeRegion]
  constructor <;> intro h c hc <;> exact (h c hc).trans or_comm

omit [DecidableEq V] in
/-- Ordinary local thinness supplies either orientation of every pair of distinct
boundary labels. Nonadjacent pairs have an empty actual bridge union. -/
theorem ThinNetworkLocalWitnesses.oriented_bridge (p : Path inc s t) (k : Nat)
    (T : ThinNetworkLocalWitnesses p k) (i j : Fin (boundaryTrace p).length) (hne : i ≠ j) :
    ∃ D : BagPath (bridgeVertices p i j) (2*k+2), D.Covers inc ∧
      (∀ x ∈ bridgeVertices p i j, x ∈ boundaryVertices p i → x ∈ D.bag 0) ∧
      (∀ x ∈ bridgeVertices p i j, x ∈ boundaryVertices p j → x ∈ D.bag D.last) := by
  classical
  by_cases hij : i.val+1=j.val
  · exact T.bridge i j hij
  by_cases hji : j.val+1=i.val
  · obtain ⟨D,hD,hfirst,hlast⟩ := T.bridge j i hji
    have heq := bridgeVertices_swap p j i
    let Q := D.reverse.recast heq
    refine ⟨Q,D.reverse.recast_covers heq (D.reverse_covers hD),?_,?_⟩
    · intro x hx hxi
      change x ∈ D.reverse.bag 0
      rw [BagPath.reverse_first]
      exact hlast x (heq.symm ▸ hx) hxi
    · intro x hx hxj
      change x ∈ D.reverse.bag D.reverse.last
      rw [BagPath.reverse_last]
      exact hfirst x (heq.symm ▸ hx) hxj
  have hempty : bridgeVertices p i j = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hr := (mem_bridgeVertices p i j x).mp hx
    have valid : ∀ a : Fin (boundaryTrace p).length,
        BoundaryValid (inc := inc) (s := s) (t := t) ((boundaryTrace p).get a) :=
      fun a => (mem_boundaryTrace p _).mp (List.get_mem _ a)
    have hi := (hr _ (valid i)).mpr (Or.inl rfl)
    have hj := (hr _ (valid j)).mpr (Or.inr rfl)
    exact (touched_boundary_indices_neighbor p x i j hne hi hj).elim hij hji
  let D := ((BagPath.single (∅ : Finset V)).weaken (by simp : (∅ : Finset V).card ≤ 2*k+2)).recast hempty.symm
  refine ⟨D,?_,?_,?_⟩
  · intro e
    refine ⟨0,Nat.zero_le _,?_⟩
    intro x hx _
    rw [hempty] at hx
    exact False.elim (Finset.notMem_empty x hx)
  · intro x hx _
    rw [hempty] at hx
    exact False.elim (Finset.notMem_empty x hx)
  · intro x hx _
    rw [hempty] at hx
    exact False.elim (Finset.notMem_empty x hx)

omit [DecidableEq V] in
/-- Exterior old local bags are obtained from ordinary thinness even when the
region is empty, without assuming an adjacency or decomposition witness. -/
theorem ThinNetworkLocalWitnesses.exterior_old_certificate (p : Path inc s t) (k : Nat)
    (T : ThinNetworkLocalWitnesses p k) (b : CutBoundary E) (removed : E)
    (hb : BoundaryValid (inc := inc) (s := s) (t := t) b)
    (hr : Cutedge inc s t removed) (hne : b ≠ .cut removed) :
    ∃ D : BagPath (exteriorOldVertices inc s t b removed) (2*k+2), D.Covers inc ∧
      (∀ x ∈ exteriorOldVertices inc s t b removed,
        BoundaryIncidence (inc := inc) (s := s) (t := t) x b → x ∈ D.bag 0) ∧
      (∀ x ∈ exteriorOldVertices inc s t b removed, inc x removed → x ∈ D.bag D.last) := by
  classical
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p b).mpr hb)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p (.cut removed)).mpr hr)
  have hij : i ≠ j := by
    intro h
    exact hne (hi.symm.trans ((congrArg (fun a => (boundaryTrace p).get a) h).trans hj))
  obtain ⟨D,hD,hfirst,hlast⟩ := T.oriented_bridge p k i j hij
  have heq : bridgeVertices p i j = exteriorOldVertices inc s t b removed := by
    ext x
    simp only [mem_bridgeVertices,mem_exteriorOldVertices,hi,hj]
  let Q := D.recast heq
  refine ⟨Q,D.recast_covers heq hD,?_,?_⟩
  · intro x hx hxb
    exact hfirst x (heq.symm ▸ hx) ((mem_boundaryVertices p i x).mpr (hi.symm ▸ hxb))
  · intro x hx hxr
    exact hlast x (heq.symm ▸ hx) ((mem_boundaryVertices p j x).mpr (hj.symm ▸ hxr))

end FiniteFlow.Hypergraph
