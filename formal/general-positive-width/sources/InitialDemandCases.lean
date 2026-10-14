import ChildDemandExtraction

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat} {G : Graph n} {O : RankedOrder n} {r : Fin n}

abbrev InitialDemand (D : IncomingDemands G O r) :=
  {i : DemandTag n // i ∈ D.indices} ⊕ {v : Fin n // v ∈ regionAdhesionSet G O r}

namespace InitialDemand
variable {D : IncomingDemands G O r} {Z : Finset (Fin n)}

def tag : InitialDemand D → DemandTag n
  | .inl i => i.val
  | .inr v => (r,v.val)

def source : InitialDemand D → Fin n
  | .inl i => D.source i.val
  | .inr _ => r

def target : InitialDemand D → Fin n
  | .inl i => D.target i.val
  | .inr v => v.val

def path (F : PrefixRoutingFamily G O r D Z) (c : InitialDemand D) :
    Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) c.source c.target :=
  match c with
  | .inl i => F.pending i.val i.property
  | .inr v => F.fresh v.val v.property

theorem allowed (F : PrefixRoutingFamily G O r D Z) (c : InitialDemand D) :
    ∀ x ∈ (c.path F).walk.vertices, rootAllowed G O r c.source c.target x := by
  cases c with
  | inl i => exact F.pending_allowed i.val i.property
  | inr v => exact F.fresh_allowed v.val v.property

theorem child_mem (F : PrefixRoutingFamily G O r D Z) (c : InitialDemand D)
    (z : Fin n) (huse : Sum.inr z ∈ (c.path F).walk.edges.map Subtype.val) :
    c.tag ∈ F.childIndices z := by
  classical
  cases c with
  | inl i =>
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨i.property,i.property,huse⟩)
  | inr v =>
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨v.val,Finset.mem_filter.mpr ⟨v.property,v.property,huse⟩,rfl⟩)

/-- Traversal endpoint extraction is consistent with the actual child demand
record for either a pending origin or a newly created root origin. -/
theorem child_endpoints (F : PrefixRoutingFamily G O r D Z) (c : InitialDemand D)
    (z : Fin n) (hz : O.rel r z)
    (e : ActiveEdge (CanonicalPrefixInc G O r Z)) (he : e.val = Sum.inr z)
    {a b : Fin n} (htr : (a,e,b) ∈ (c.path F).walk.traversals) :
    (F.childDemands z hz).source c.tag = a ∧ (F.childDemands z hz).target c.tag = b := by
  classical
  have hedge : e ∈ (c.path F).walk.edges := by
    rw [← HWalk.traversal_edges]
    exact List.mem_map.mpr ⟨(a,e,b),htr,rfl⟩
  have hraw : Sum.inr z ∈ (c.path F).walk.edges.map Subtype.val :=
    List.mem_map.mpr ⟨e,hedge,he⟩
  cases c with
  | inl i =>
    have hi : i.val ∈ F.pendingUses z := Finset.mem_filter.mpr ⟨i.property,i.property,hraw⟩
    let B := F.pendingPass z i.val hi
    have hBe : B.edge = e := Subtype.ext (B.edge_id.trans he.symm)
    have hend := B.endpoints_exact (hBe.symm ▸ htr)
    change (F.childEndpoints z i.val).1 = a ∧ (F.childEndpoints z i.val).2 = b
    simpa only [PrefixRoutingFamily.childEndpoints,dite_eq_left hi] using ⟨hend.1.symm,hend.2.symm⟩
  | inr v =>
    have hv : v.val ∈ F.freshUses z := Finset.mem_filter.mpr ⟨v.property,v.property,hraw⟩
    have hn : (r,v.val) ∉ F.pendingUses z := by
      intro hi
      exact O.irrefl r (D.above (r,v.val) (Finset.mem_filter.mp hi).1)
    let B := F.freshPass z v.val hv
    have hBe : B.edge = e := Subtype.ext (B.edge_id.trans he.symm)
    have hend := B.endpoints_exact (hBe.symm ▸ htr)
    change (F.childEndpoints z (r,v.val)).1 = a ∧ (F.childEndpoints z (r,v.val)).2 = b
    simpa only [PrefixRoutingFamily.childEndpoints,dite_eq_right hn,dite_eq_left hv] using
      ⟨hend.1.symm,hend.2.symm⟩

end InitialDemand
end StackSorting.LowPathwidthParts
