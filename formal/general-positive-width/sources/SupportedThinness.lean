import SupportedBagPaths

namespace FiniteFlow.Hypergraph
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {inc : V → E → Prop}

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem supported_valid_iff (S : Set V) (support : ∀ x e, inc x e → x ∈ S)
    (s t : S) (b : CutBoundary E) :
    BoundaryValid (inc := SupportedIncidence (inc := inc) S) (s := s) (t := t) b ↔
      BoundaryValid (inc := inc) (s := s.val) (t := t.val) b := by
  cases b with
  | source => rfl
  | sink => rfl
  | cut e => exact supported_cutedge_iff S support s t e

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem supported_boundary_incidence_iff (S : Set V) (s t x : S) (b : CutBoundary E) :
    BoundaryIncidence (inc := SupportedIncidence (inc := inc) S) (s := s) (t := t) x b ↔
      BoundaryIncidence (inc := inc) (s := s.val) (t := t.val) x.val b := by
  cases b <;> simp [BoundaryIncidence,SupportedIncidence,Subtype.ext_iff]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem supported_appendix_iff (S : Set V) (support : ∀ x e, inc x e → x ∈ S)
    (s t x : S) (e : E) :
    AppendixRegion (inc := SupportedIncidence (inc := inc) S) (s := s) (t := t) e x ↔
      AppendixRegion (inc := inc) (s := s.val) (t := t.val) e x.val := by
  simp only [AppendixRegion,supported_valid_iff S support,supported_touches_iff S support]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem supported_bridge_iff (S : Set V) (support : ∀ x e, inc x e → x ∈ S)
    (s t x : S) (a b : CutBoundary E) :
    BridgeRegion (inc := SupportedIncidence (inc := inc) S) (s := s) (t := t) a b x ↔
      BridgeRegion (inc := inc) (s := s.val) (t := t.val) a b x.val := by
  simp only [BridgeRegion,supported_valid_iff S support,supported_touches_iff S support]

/-- Removing unused ambient vertices preserves the concrete local certificates.
This is the support restriction needed before applying the connected 5.7 theorem. -/
theorem local_thinness_onSupport (S : Set V) [Fintype S] (support : ∀ x e, inc x e → x ∈ S)
    (s t : S) (p : Path inc s.val t.val) (q : Path (SupportedIncidence (inc := inc) S) s t)
    (k : Nat) (T : ThinNetworkLocalWitnesses p k) : ThinNetworkLocalWitnesses q k := by
  classical
  constructor
  · intro e he
    obtain ⟨D,hD,hfirst⟩ := T.appendix e ((supported_cutedge_iff S support s t e).mp he)
    have heq : supportedFinset S (appendixVertices inc s.val t.val e) =
        appendixVertices (SupportedIncidence (inc := inc) S) s t e := by
      ext x
      simp only [mem_supportedFinset,mem_appendixVertices,supported_appendix_iff S support]
    let A := (D.onSupport S).recast heq
    refine ⟨A,(D.onSupport S).recast_covers heq (D.onSupport_covers S hD),?_⟩
    intro x hx hxe
    apply (mem_supportedFinset S (D.bag 0) x).mpr
    exact hfirst x.val ((mem_supportedFinset S _ x).mp (heq.symm ▸ hx)) hxe
  · intro i j hij
    let a := (boundaryTrace q).get i
    let b := (boundaryTrace q).get j
    have valid : ∀ l : Fin (boundaryTrace q).length,
        BoundaryValid (inc := inc) (s := s.val) (t := t.val) ((boundaryTrace q).get l) :=
      fun l => (supported_valid_iff S support s t _).mp
        ((mem_boundaryTrace q _).mp (List.get_mem _ l))
    have hab : a ≠ b := by
      intro he
      have before := (boundaryTrace_get_before q i j).mpr (by change i.val < j.val; omega)
      change BoundaryBefore q a b at before
      rw [he] at before
      exact boundaryBefore_irrefl q _ before
    obtain ⟨u,hu⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p a).mpr (valid i))
    obtain ⟨v,hv⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p b).mpr (valid j))
    have huv : u ≠ v := by
      intro he
      exact hab (hu.symm.trans ((congrArg (fun l => (boundaryTrace p).get l) he).trans hv))
    obtain ⟨D,hD,hfirst,hlast⟩ := T.oriented_bridge p k u v huv
    have heq : supportedFinset S (bridgeVertices p u v) = bridgeVertices q i j := by
      ext x
      simp only [mem_supportedFinset,mem_bridgeVertices,hu,hv,supported_bridge_iff S support,a,b]
    let A := (D.onSupport S).recast heq
    refine ⟨A,(D.onSupport S).recast_covers heq (D.onSupport_covers S hD),?_,?_⟩
    · intro x hx hxi
      have hi := (supported_boundary_incidence_iff S s t x a).mp ((mem_boundaryVertices q i x).mp hxi)
      apply (mem_supportedFinset S (D.bag 0) x).mpr
      exact hfirst x.val ((mem_supportedFinset S _ x).mp (heq.symm ▸ hx))
        ((mem_boundaryVertices p u x.val).mpr (hu.symm ▸ hi))
    · intro x hx hxj
      have hj := (supported_boundary_incidence_iff S s t x b).mp ((mem_boundaryVertices q j x).mp hxj)
      apply (mem_supportedFinset S (D.bag D.last) x).mpr
      exact hlast x.val ((mem_supportedFinset S _ x).mp (heq.symm ▸ hx))
        ((mem_boundaryVertices p v x.val).mpr (hv.symm ▸ hj))

end FiniteFlow.Hypergraph
