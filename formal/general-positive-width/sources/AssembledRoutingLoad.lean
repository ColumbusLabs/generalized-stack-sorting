import AssembledIndexedRoutes

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}
namespace ChildRoutingSolutions
variable {G : Graph n} {O : RankedOrder n} {r : Fin n} {D : IncomingDemands G O r}
    {k : Nat} {Z : Finset (Fin n)} {hp : RelativePrefix O r Z}
    {F : PrefixRoutingFamily G O r D Z} (C : ChildRoutingSolutions G O r D k Z hp F)

/-- A support hit of a spliced initial demand induces a hit of the child's
incoming route with the identical original tag. -/
theorem initial_hit_child (c : InitialDemand D) (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) (a x : Fin n)
    (hza : Cone O z a) (hax : Cone O a x)
    (hx : x ∈ (C.splicedWalk c).support) :
    c.tag ∈ (C.child z hz).routes.pendingTraffic a := by
  classical
  obtain ⟨hi,hs⟩ := C.spliced_hits_child c z hz x hx (cone_trans O hza hax)
  exact Finset.mem_filter.mpr ⟨hi,hi,x,hs,hax⟩

/-- No demand is merged: the injection is literally the identity on global
(base,target) tags, including repeated current endpoint pairs. -/
theorem load_union_subset_child (z : Fin n)
    (hz : Frontier (clippedParent O r) Z z) (a : Fin n)
    (ha : a ∈ (C.child z hz).selected.nodes) :
    C.assembledRoutes.internalLoad a ∪ C.assembledRoutes.pendingTraffic a ⊆
      (C.child z hz).routes.internalLoad a ∪ (C.child z hz).routes.pendingTraffic a := by
  classical
  intro i hi
  have hza := (C.child z hz).selected.inside a ha
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨hbase,hv,hrel,x,hx,hax⟩ := (Finset.mem_filter.mp hi).2
    by_cases hir : i.1 = r
    · apply Finset.mem_union_right
      rcases i with ⟨q,v⟩
      change q = r at hir
      subst q
      have hx' : x ∈ (C.splicedWalk (.inr ⟨v,hv⟩)).support := by
        change x ∈ (C.outgoing r hbase v hv).support at hx
        unfold outgoing at hx
        split at hx
        · exact hx
        · contradiction
      exact C.initial_hit_child (.inr ⟨v,hv⟩) z hz a x hza hax hx'
    · have hchild := assembled_ancestor_child O r Z hp
        (fun w hw => (C.child w hw).selected) z hz hza hbase hrel hir
      apply Finset.mem_union_left
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hchild,hv,hrel,x,?_,hax⟩
      change x ∈ (C.outgoing i.1 hbase i.2 hv).support at hx
      rw [C.outgoing_child z hz i.1 hchild hbase i.2 hv] at hx
      exact hx
  · obtain ⟨hi,hi',x,hx,hax⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_union_right
    exact C.initial_hit_child (.inl ⟨i,hi'⟩) z hz a x hza hax hx

theorem root_internal_empty : C.assembledRoutes.internalLoad r = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hb,_,hr,_⟩ := (Finset.mem_filter.mp hi).2
  rcases C.assembledSelection.inside i.1 hb with h | h
  · exact O.irrefl r (O.trans h hr)
  · exact O.irrefl r (by simpa only [h] using hr)

/-- The additive residual bound is preserved by the actual assembled walks,
using recursive child bounds and the original incoming index cap. -/
theorem assembled_bounded (hcap : D.indices.card ≤ 2*k^3) :
    C.assembledRoutes.Bounded k := by
  classical
  apply (C.assembledRoutes.bounded_union_iff k).mpr
  intro a ha
  rcases (assembled_mem O r Z hp (fun z hz => (C.child z hz).selected) a).mp ha with he | ⟨z,hz,ha⟩
  · subst a
    rw [C.root_internal_empty,Finset.empty_union]
    exact (Finset.card_le_card (C.assembledRoutes.pendingTraffic_subset r)).trans hcap
  · exact (Finset.card_le_card (C.load_union_subset_child z hz a ha)).trans
      (((C.child z hz).routes.bounded_union_iff k).mp (C.child z hz).bounded a ha)

end ChildRoutingSolutions
end StackSorting.LowPathwidthParts
