import CutedgePrefix
import HWalkEdgeOrder

/-!
# Actual cutedge order (Bojanczyk--Pilipczuk Lemma 5.3)

The sequence is the cutedge filter of an actual simple path. Equality of the
filtered sequences is proved by prefix splicing, rather than assumed.
-/
namespace FiniteFlow.Hypergraph

variable {V E : Type*} {inc : V → E → Prop} {s t : V}

theorem cutedge_idxOf_lt_iff [DecidableEq E] (p q : Path inc s t)
    {e f : E} (he : Cutedge inc s t e) (hf : Cutedge inc s t f) :
    p.walk.edges.idxOf e < p.walk.edges.idxOf f ↔
      q.walk.edges.idxOf e < q.walk.edges.idxOf f := by
  obtain ⟨a, b, pp, ps, ha, hb, hp, hpf, _, _, _⟩ :=
    p.walk.split_at_edge_nodup p.edges_nodup (hf p)
  obtain ⟨c, d, qp, qs, hc, hd, hq, hqf, _, _, _⟩ :=
    q.walk.split_at_edge_nodup q.edges_nodup (hf q)
  rw [hp, hq]
  exact (mem_pre_iff_idxOf_lt pp.edges ps.edges e f hpf).symm.trans
    ((cutedge_prefix_mem_iff he p q pp ps qp qs hp hq ha hb hc hd).trans
      (mem_pre_iff_idxOf_lt qp.edges qs.edges e f hqf))

noncomputable def cutedgeTrace (p : Path inc s t) : List E := by
  classical
  exact p.walk.edges.filter (fun e => decide (Cutedge inc s t e))

@[simp] theorem mem_cutedgeTrace (p : Path inc s t) (e : E) :
    e ∈ cutedgeTrace p ↔ Cutedge inc s t e := by
  classical
  simp only [cutedgeTrace, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h p, h⟩⟩

theorem cutedgeTrace_nodup (p : Path inc s t) : (cutedgeTrace p).Nodup := by
  classical
  exact p.edges_nodup.filter _

theorem cutedgeTrace_pairwise [DecidableEq E] (p : Path inc s t) :
    (cutedgeTrace p).Pairwise
      (fun e f => p.walk.edges.idxOf e < p.walk.edges.idxOf f) := by
  classical
  exact (pairwise_idxOf p.walk.edges p.edges_nodup).filter _

/-- Every actual simple source--sink path has exactly the same ordered trace
of unavoidable edge identifiers. This also covers empty traces. -/
theorem cutedgeTrace_eq (p q : Path inc s t) : cutedgeTrace p = cutedgeTrace q := by
  classical
  have hq : (cutedgeTrace q).Pairwise
      (fun e f => p.walk.edges.idxOf e < p.walk.edges.idxOf f) := by
    apply (cutedgeTrace_pairwise q).imp_of_mem
    intro e f he hf hlt
    exact (cutedge_idxOf_lt_iff q p ((mem_cutedgeTrace q e).mp he)
      ((mem_cutedgeTrace q f).mp hf)).mp hlt
  have hpq : (cutedgeTrace p).Perm (cutedgeTrace q) := by
    apply (List.perm_ext_iff_of_nodup (cutedgeTrace_nodup p)
      (cutedgeTrace_nodup q)).mpr
    intro e
    exact (mem_cutedgeTrace p e).trans (mem_cutedgeTrace q e).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ h₁ h₂ => (Nat.lt_asymm h₁ h₂).elim)
    (cutedgeTrace_pairwise p) hq hpq

/-- The cutedge sequence is constructed from connectivity. No ordering witness
or two-path witness is required as an input. -/
theorem exists_cutedge_sequence (connected : Nonempty (HWalk inc s t)) :
    ∃ es : List E, es.Nodup ∧
      (∀ e, e ∈ es ↔ Cutedge inc s t e) ∧
      ∀ p : Path inc s t, cutedgeTrace p = es := by
  obtain ⟨w⟩ := connected
  obtain ⟨p, _⟩ := w.exists_path
  exact ⟨cutedgeTrace p, cutedgeTrace_nodup p, mem_cutedgeTrace p,
    fun q => cutedgeTrace_eq q p⟩

end FiniteFlow.Hypergraph
