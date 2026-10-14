import ThinNetworkGlobalAssembly

namespace FiniteFlow.Hypergraph
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {inc : V → E → Prop} {s t : V}

noncomputable def appendixVertices (inc : V → E → Prop) (s t : V) (e : E) : Finset V := by
  classical
  exact Finset.univ.filter (AppendixRegion (inc := inc) (s := s) (t := t) e)

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem mem_appendixVertices (inc : V → E → Prop) (s t : V) (e : E) (x : V) :
    x ∈ appendixVertices inc s t e ↔ AppendixRegion (inc := inc) (s := s) (t := t) e x := by
  classical
  simp [appendixVertices]

/-- The local clauses of thinness, on actual cutedge component unions. The
appendix first-bag condition is retained even though 5.7 itself does not need it. -/
structure ThinNetworkLocalWitnesses (p : Path inc s t) (k : Nat) : Prop where
  appendix : ∀ e, Cutedge inc s t e →
    ∃ D : BagPath (appendixVertices inc s t e) (k+1), D.Covers inc ∧
      ∀ x ∈ appendixVertices inc s t e, inc x e → x ∈ D.bag 0
  bridge : ∀ i j : Fin (boundaryTrace p).length, i.val+1=j.val →
    ∃ D : BagPath (bridgeVertices p i j) (2*k+2), D.Covers inc ∧
      (∀ x ∈ bridgeVertices p i j, x ∈ boundaryVertices p i → x ∈ D.bag 0) ∧
      (∀ x ∈ bridgeVertices p i j, x ∈ boundaryVertices p j → x ∈ D.bag D.last)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem oneBoundary_source_impossible
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (x : V) :
    ¬ OneBoundaryRegion (inc := inc) (s := s) (t := t) .source x := by
  intro h
  rcases component_meets_cutedge_or_both_terminals connected x with
    ⟨e,y,he,hy,hxy⟩ | ⟨_,ht⟩
  · have bad := (h (.cut e) he).mp ⟨y,hy,hxy⟩
    cases bad
  · have bad := (h .sink trivial).mp ht
    cases bad

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem oneBoundary_sink_impossible
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (x : V) :
    ¬ OneBoundaryRegion (inc := inc) (s := s) (t := t) .sink x := by
  intro h
  rcases component_meets_cutedge_or_both_terminals connected x with
    ⟨e,y,he,hy,hxy⟩ | ⟨hs,_⟩
  · have bad := (h (.cut e) he).mp ⟨y,hy,hxy⟩
    cases bad
  · have bad := (h .source trivial).mp hs
    cases bad

/-- Supply terminal empty certificates and choose the actual local witnesses.
The padded source/sink pieces therefore add no hypothesis to ordinary thinness. -/
noncomputable def localWitnesses_to_certificates
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (k : Nat)
    (T : ThinNetworkLocalWitnesses p k) : ThinBagCertificates p k := by
  classical
  have adata : ∀ i : Fin (boundaryTrace p).length,
      Nonempty {D : BagPath (oneBoundaryVertices p i) (k+1) // D.Covers inc} := by
    intro i
    have hv := (mem_boundaryTrace p _).mp (List.get_mem _ i)
    cases hb : (boundaryTrace p).get i with
    | source =>
      have hemp : oneBoundaryVertices p i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hr := (mem_oneBoundaryVertices p i x).mp hx
        rw [hb] at hr
        exact oneBoundary_source_impossible connected x hr
      let D0 : BagPath (∅ : Finset V) (k+1) := (BagPath.single ∅).weaken (by simp)
      have hc : D0.Covers inc := BagPath.single_covers ∅ inc
      exact ⟨⟨D0.recast hemp.symm,D0.recast_covers hemp.symm hc⟩⟩
    | sink =>
      have hemp : oneBoundaryVertices p i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hr := (mem_oneBoundaryVertices p i x).mp hx
        rw [hb] at hr
        exact oneBoundary_sink_impossible connected x hr
      let D0 : BagPath (∅ : Finset V) (k+1) := (BagPath.single ∅).weaken (by simp)
      have hc : D0.Covers inc := BagPath.single_covers ∅ inc
      exact ⟨⟨D0.recast hemp.symm,D0.recast_covers hemp.symm hc⟩⟩
    | cut e =>
      have he : Cutedge inc s t e := by simpa only [hb,BoundaryValid] using hv
      obtain ⟨D,hD,_⟩ := T.appendix e he
      have heq : appendixVertices inc s t e = oneBoundaryVertices p i := by
        ext x
        simp only [appendixVertices,oneBoundaryVertices,Finset.mem_filter,Finset.mem_univ,true_and,
          hb,AppendixRegion,OneBoundaryRegion]
      exact ⟨⟨D.recast heq,D.recast_covers heq hD⟩⟩
  let a := fun i => Classical.choice (adata i)
  let b := fun i j h => Classical.choose (T.bridge i j h)
  exact {
    appendix := fun i => (a i).val
    appendix_cover := fun i => (a i).property
    bridge := b
    bridge_cover := fun i j h => (Classical.choose_spec (T.bridge i j h)).1
    bridge_first := fun i j h => (Classical.choose_spec (T.bridge i j h)).2.1
    bridge_last := fun i j h => (Classical.choose_spec (T.bridge i j h)).2.2
  }

/-- Rank-qualified B–P Lemma 5.7: ordinary local thinness witnesses yield an
actual full-hypergraph path decomposition with bags of cardinality at most
2k+2 (width at most 2k+1). The required rank bound is not silently assumed. -/
theorem ranked_thin_network_has_bag_path
    (connected : ∀ x y, Nonempty (HWalk inc x y)) (p : Path inc s t) (k : Nat)
    (T : ThinNetworkLocalWitnesses p k)
    (rank : ∀ e, Cutedge inc s t e → (hyperedgeVertices inc e).card ≤ k+1) :
    ∃ D : BagPath (Finset.univ : Finset V) (2*k+2), D.Covers inc :=
  thin_network_global_bag_assembly connected p k
    (localWitnesses_to_certificates connected p k T) rank

end FiniteFlow.Hypergraph
