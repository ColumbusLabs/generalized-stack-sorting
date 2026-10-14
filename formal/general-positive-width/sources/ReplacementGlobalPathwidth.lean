import ReplacementLocalThinness

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} [Fintype V] [DecidableEq V] [DecidableEq E] [DecidableEq F]
variable {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}
namespace ReplacementFrame

omit [Fintype V] [DecidableEq V] [DecidableEq E] [DecidableEq F] in
theorem replacement_connected (R : ReplacementFrame old inserted s t removed)
    (old_to_source : ∀ x ∈ R.oldVertices, Nonempty (HWalk old x s))
    (new_to_anchor : ∀ x ∈ R.newVertices, Nonempty (HWalk inserted x R.anchor))
    (support : ∀ x, x ∈ R.oldVertices ∨ x ∈ R.newVertices) :
    ∀ x y, Nonempty (HWalk (ReplacementIncidence old inserted removed) x y) := by
  have to_source : ∀ x, Nonempty (HWalk (ReplacementIncidence old inserted removed) x s) := by
    intro x
    rcases support x with hx | hx
    · obtain ⟨w⟩ := old_to_source x hx
      exact ⟨liftReplacement removed R.inserted_connects w⟩
    · obtain ⟨w⟩ := new_to_anchor x hx
      obtain ⟨v⟩ := old_to_source R.anchor (R.old_support R.anchor removed R.anchor_incident)
      exact ⟨(w.mapEdges (inc' := ReplacementIncidence old inserted removed) Sum.inr
        (fun _ _ h => h)).append (liftReplacement removed R.inserted_connects v)⟩
  intro x y
  obtain ⟨wx⟩ := to_source x
  obtain ⟨wy⟩ := to_source y
  exact ⟨wx.append wy.reverse⟩

omit [DecidableEq V] [DecidableEq E] [DecidableEq F] in
theorem replacement_cutedge_rank (R : ReplacementFrame old inserted s t removed)
    (k : Nat) (K : Finset V) (small : K.card ≤ k+1)
    (K_exact : ∀ x, x ∈ R.newVertices ↔ x ∈ K)
    (rank : ∀ e, Cutedge old s t e → (hyperedgeVertices old e).card ≤ k+1) :
    ∀ e, Cutedge (ReplacementIncidence old inserted removed) s t e →
      (hyperedgeVertices (ReplacementIncidence old inserted removed) e).card ≤ k+1 := by
  classical
  intro e he
  cases e with
  | inl e => exact rank e.val (replacement_cutedge_old_implies removed R.inserted_connects e he)
  | inr f =>
    apply (Finset.card_le_card ?_).trans small
    intro x hx
    have hxf : inserted x f := (Finset.mem_filter.mp hx).2
    exact (K_exact x).mp (R.new_support x f hxf)

/-- Combined rank-qualified 5.7 and actual 5.8 construction: the replacement
has a full-hyperedge path decomposition. Rank is derived from the old explicit
cutedge-rank premise and the size of the inserted vertex set. -/
theorem replacement_has_global_bag_path
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t) (k : Nat)
    (T : ThinNetworkLocalWitnesses p k) (K : Finset V) (small : K.card ≤ k+1)
    (K_exact : ∀ x, x ∈ R.newVertices ↔ x ∈ K)
    (old_to_source : ∀ x ∈ R.oldVertices, Nonempty (HWalk old x s))
    (new_to_anchor : ∀ x ∈ R.newVertices, Nonempty (HWalk inserted x R.anchor))
    (removed_in_new : ∀ x, old x removed → x ∈ R.newVertices)
    (support : ∀ x, x ∈ R.oldVertices ∨ x ∈ R.newVertices)
    (rank : ∀ e, Cutedge old s t e → (hyperedgeVertices old e).card ≤ k+1) :
    ∃ D : BagPath (Finset.univ : Finset V) (2*k+2),
      D.Covers (ReplacementIncidence old inserted removed) := by
  obtain ⟨q,hq⟩ := R.replacement_has_thin_path p k T K small K_exact old_to_source
    new_to_anchor removed_in_new support
  exact ranked_thin_network_has_bag_path (R.replacement_connected old_to_source new_to_anchor support)
    q k hq (R.replacement_cutedge_rank k K small K_exact rank)

end ReplacementFrame
end FiniteFlow.Hypergraph
