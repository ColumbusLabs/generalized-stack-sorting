import BoundaryTraversalDemands

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}
attribute [local instance] Classical.propDecidable
namespace PrefixRoutingFamily
variable {G : Graph n} {O : RankedOrder n} {r : Fin n} {D : IncomingDemands G O r}
    {Z : Finset (Fin n)} (F : PrefixRoutingFamily G O r D Z)

noncomputable def childIndices (z : Fin n) : Finset (DemandTag n) := by
  classical
  exact F.pendingUses z ∪ (F.freshUses z).image (fun v => (r,v))

theorem child_halves_disjoint (z : Fin n) :
    Disjoint (F.pendingUses z) ((F.freshUses z).image (fun v => (r,v))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨v,_hv,he⟩ := Finset.mem_image.mp hj
  have hI : i ∈ D.indices := (Finset.mem_filter.mp hi).1
  have hrel := D.above i hI
  have hbase : r = i.1 := congrArg Prod.fst he
  exact O.irrefl r (by simpa only [← hbase] using hrel)

theorem childIndices_card (z : Fin n) :
    (F.childIndices z).card = (F.pendingUses z).card + (F.freshUses z).card := by
  classical
  rw [childIndices,Finset.card_union_of_disjoint (F.child_halves_disjoint z)]
  congr 1
  exact Finset.card_image_of_injective _ (fun _ _ he => congrArg Prod.snd he)

noncomputable def pendingPass (z : Fin n) (i : DemandTag n) (hi : i ∈ F.pendingUses z) :
    BoundaryPass (F.pending i (Finset.mem_filter.mp hi).1) z := by
  classical
  apply boundaryPass
  obtain ⟨hI,hraw⟩ := (Finset.mem_filter.mp hi).2
  exact hraw

noncomputable def freshPass (z v : Fin n) (hv : v ∈ F.freshUses z) :
    BoundaryPass (F.fresh v (Finset.mem_filter.mp hv).1) z := by
  classical
  apply boundaryPass
  obtain ⟨hA,hraw⟩ := (Finset.mem_filter.mp hv).2
  exact hraw

noncomputable def childEndpoints (z : Fin n) (i : DemandTag n) : Fin n × Fin n := by
  classical
  exact if hi : i ∈ F.pendingUses z then ((F.pendingPass z i hi).before,(F.pendingPass z i hi).after)
    else if hv : i.2 ∈ F.freshUses z then ((F.freshPass z i.2 hv).before,(F.freshPass z i.2 hv).after)
    else (z,z)

/-- Child demands are the actual traversal endpoints, with the same global
origin tags. No new demand family, endpoint adhesion or cap is assumed. -/
noncomputable def childDemands (z : Fin n) (hz : O.rel r z) : IncomingDemands G O z where
  indices := F.childIndices z
  source i := (F.childEndpoints z i).1
  target i := (F.childEndpoints z i).2
  endpoints := by
    classical
    intro i hi
    rcases Finset.mem_union.mp hi with hp | hf
    · simpa only [childEndpoints,dite_eq_left hp] using (F.pendingPass z i hp).endpoints_in_adhesion
    · obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hf
      have htarget : i.2 ∈ F.freshUses z := by simpa only [← he] using hv
      have hn : i ∉ F.pendingUses z := fun hp =>
        Finset.disjoint_left.mp (F.child_halves_disjoint z) hp (Finset.mem_image.mpr ⟨v,hv,he⟩)
      simpa only [childEndpoints,dite_eq_right hn,dite_eq_left htarget] using
        (F.freshPass z i.2 htarget).endpoints_in_adhesion
  above := by
    classical
    intro i hi
    rcases Finset.mem_union.mp hi with hp | hf
    · exact O.trans (D.above i (Finset.mem_filter.mp hp).1) hz
    · obtain ⟨v,_hv,he⟩ := Finset.mem_image.mp hf
      have hbase := congrArg Prod.fst he
      exact hbase ▸ hz

theorem childDemands_cap (k : Nat) (h : F.Bounded k) (z : Fin n) (hz : O.rel r z) :
    (F.childDemands z hz).indices.card ≤ 2*k^3 := by
  change (F.childIndices z).card ≤ 2*k^3
  rw [F.childIndices_card]
  exact h z

end PrefixRoutingFamily
end StackSorting.LowPathwidthParts
