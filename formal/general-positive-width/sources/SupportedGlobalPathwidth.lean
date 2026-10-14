import SupportedThinness

namespace FiniteFlow.Hypergraph
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {inc : V → E → Prop}

/-- Rank-qualified 5.7 on the actual supported vertex subtype. Neither unused
ambient vertices nor an assumed global pathwidth enter the construction. -/
theorem supported_thin_network_has_bag_path (S : Set V) [Fintype S]
    (support : ∀ x e, inc x e → x ∈ S) (s t : S)
    (connected : ∀ x ∈ S, Nonempty (HWalk inc x s.val))
    (p : Path inc s.val t.val) (k : Nat) (T : ThinNetworkLocalWitnesses p k)
    (rank : ∀ e, Cutedge inc s.val t.val e → (hyperedgeVertices inc e).card ≤ k+1) :
    ∃ D : BagPath (Finset.univ : Finset S) (2*k+2),
      D.Covers (SupportedIncidence (inc := inc) S) := by
  classical
  obtain ⟨q,_⟩ := (p.walk.onSupport S support s.property t.property).exists_path
  have hc : ∀ x y : S, Nonempty (HWalk (SupportedIncidence (inc := inc) S) x y) := by
    intro x y
    obtain ⟨wx⟩ := connected x.val x.property
    obtain ⟨wy⟩ := connected y.val y.property
    exact ⟨(wx.append wy.reverse).onSupport S support x.property y.property⟩
  have hr : ∀ e, Cutedge (SupportedIncidence (inc := inc) S) s t e →
      (hyperedgeVertices (SupportedIncidence (inc := inc) S) e).card ≤ k+1 := by
    intro e he
    have heq : hyperedgeVertices (SupportedIncidence (inc := inc) S) e =
        supportedFinset S (hyperedgeVertices inc e) := by
      ext x
      rw [mem_supportedFinset]
      constructor
      · intro hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
      · intro hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
    rw [heq]
    exact (supportedFinset_card_le S _).trans (rank e ((supported_cutedge_iff S support s t e).mp he))
  exact ranked_thin_network_has_bag_path hc q k (local_thinness_onSupport S support s t p q k T) hr

end FiniteFlow.Hypergraph
