import HypergraphEdgeEquivalence

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {inc : V → E → Prop} {inc' : V → F → Prop} {s t : V}
namespace IncidenceEquiv
variable (Q : IncidenceEquiv inc inc')

theorem appendix_iff (e : E) (x : V) :
    AppendixRegion (inc := inc') (s := s) (t := t) (Q.edge e) x ↔
      AppendixRegion (inc := inc) (s := s) (t := t) e x := by
  constructor
  · intro h b hb
    have hn := h (Q.boundary b) ((Q.boundary_valid_iff b).mpr hb)
    constructor
    · intro hx
      exact Q.boundary.injective (hn.mp ((Q.boundary_touch_iff x b).mpr hx))
    · intro he
      subst b
      exact (Q.boundary_touch_iff x (.cut e)).mp (hn.mpr rfl)
  · intro h b hb
    obtain ⟨a,rfl⟩ := Q.boundary.surjective b
    have ho := h a ((Q.boundary_valid_iff a).mp hb)
    constructor
    · intro hx
      exact congrArg Q.boundary (ho.mp ((Q.boundary_touch_iff x a).mp hx))
    · intro he
      have hae : a = .cut e := Q.boundary.injective he
      exact (Q.boundary_touch_iff x a).mpr (ho.mpr hae)

theorem bridge_iff (a b : CutBoundary E) (x : V) :
    BridgeRegion (inc := inc') (s := s) (t := t) (Q.boundary a) (Q.boundary b) x ↔
      BridgeRegion (inc := inc) (s := s) (t := t) a b x := by
  constructor
  · intro h c hc
    have hn := h (Q.boundary c) ((Q.boundary_valid_iff c).mpr hc)
    constructor
    · intro hx
      exact (hn.mp ((Q.boundary_touch_iff x c).mpr hx)).imp (fun h => Q.boundary.injective h) (fun h => Q.boundary.injective h)
    · intro he
      exact (Q.boundary_touch_iff x c).mp (hn.mpr (he.imp (congrArg Q.boundary) (congrArg Q.boundary)))
  · intro h c hc
    obtain ⟨d,rfl⟩ := Q.boundary.surjective c
    have ho := h d ((Q.boundary_valid_iff d).mp hc)
    constructor
    · intro hx
      exact (ho.mp ((Q.boundary_touch_iff x d).mp hx)).imp (congrArg Q.boundary) (congrArg Q.boundary)
    · intro he
      exact (Q.boundary_touch_iff x d).mpr (ho.mpr (he.imp (fun h => Q.boundary.injective h) (fun h => Q.boundary.injective h)))

include Q in
/-- Local thinness depends on actual incidences and boundary labels, not the
particular names used for the finite hyperedge identifiers. -/
theorem local_thinness_transport [Fintype V] [DecidableEq E] [DecidableEq F]
    (p : Path inc s t) (q : Path inc' s t) (k : Nat) (T : ThinNetworkLocalWitnesses p k) :
    ThinNetworkLocalWitnesses q k := by
  classical
  constructor
  · intro f hf
    obtain ⟨e,rfl⟩ := Q.edge.surjective f
    obtain ⟨D,hD,hfirst⟩ := T.appendix e ((Q.cutedge_iff e).mp hf)
    have heq : appendixVertices inc s t e = appendixVertices inc' s t (Q.edge e) := by
      ext x
      simp only [mem_appendixVertices,Q.appendix_iff]
    let A := D.recast heq
    refine ⟨A,Q.covers A (D.recast_covers heq hD),?_⟩
    intro x hx hxf
    exact hfirst x (heq.symm ▸ hx) ((Q.incidence x e).mp hxf)
  · intro i j hij
    let a := Q.boundary.symm ((boundaryTrace q).get i)
    let b := Q.boundary.symm ((boundaryTrace q).get j)
    have hai : Q.boundary a = (boundaryTrace q).get i := Q.boundary.apply_symm_apply _
    have hbj : Q.boundary b = (boundaryTrace q).get j := Q.boundary.apply_symm_apply _
    have valid : ∀ l : Fin (boundaryTrace q).length,
        BoundaryValid (inc := inc') (s := s) (t := t) ((boundaryTrace q).get l) :=
      fun l => (mem_boundaryTrace q _).mp (List.get_mem _ l)
    have ha : BoundaryValid (inc := inc) (s := s) (t := t) a :=
      (Q.boundary_valid_iff a).mp (hai.symm ▸ valid i)
    have hb : BoundaryValid (inc := inc) (s := s) (t := t) b :=
      (Q.boundary_valid_iff b).mp (hbj.symm ▸ valid j)
    have hab : a ≠ b := by
      intro he
      have heq : (boundaryTrace q).get i = (boundaryTrace q).get j := hai.symm.trans ((congrArg Q.boundary he).trans hbj)
      have before := (boundaryTrace_get_before q i j).mpr (by change i.val < j.val; omega)
      rw [heq] at before
      exact boundaryBefore_irrefl q _ before
    obtain ⟨u,hu⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p a).mpr ha)
    obtain ⟨v,hv⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p b).mpr hb)
    have huv : u ≠ v := by
      intro he
      exact hab (hu.symm.trans ((congrArg (fun l => (boundaryTrace p).get l) he).trans hv))
    obtain ⟨D,hD,hfirst,hlast⟩ := T.oriented_bridge p k u v huv
    have heq : bridgeVertices p u v = bridgeVertices q i j := by
      ext x
      simp only [mem_bridgeVertices,hu,hv,← hai,← hbj,Q.bridge_iff]
    let A := D.recast heq
    refine ⟨A,Q.covers A (D.recast_covers heq hD),?_,?_⟩
    · intro x hx hxi
      have hi' := (mem_boundaryVertices q i x).mp hxi
      have hiold := (Q.boundary_incidence_iff x a).mp (hai.symm ▸ hi')
      exact hfirst x (heq.symm ▸ hx) ((mem_boundaryVertices p u x).mpr (hu.symm ▸ hiold))
    · intro x hx hxj
      have hj' := (mem_boundaryVertices q j x).mp hxj
      have hjold := (Q.boundary_incidence_iff x b).mp (hbj.symm ▸ hj')
      exact hlast x (heq.symm ▸ hx) ((mem_boundaryVertices p v x).mpr (hv.symm ▸ hjold))

end IncidenceEquiv
end FiniteFlow.Hypergraph
