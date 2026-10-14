import IndexedRoutingDemands
import ContractedAdhesionGeometry

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

/-- Concrete original-edge routes for the two sorts of demands in the
subtree induction. Outgoing routes retain their original (base,target) tags. -/
structure IndexedRoutes (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (D : IncomingDemands G O r) (A : RootedSelection O r) where
  incoming : ∀ i ∈ D.indices, (AdhesionGuidance.originalGraph G).Walk (D.source i) (D.target i)
  outgoing : ∀ a ∈ A.nodes, ∀ v ∈ regionAdhesionSet G O a,
    (AdhesionGuidance.originalGraph G).Walk a v
  incoming_inside : ∀ i hi x, x ∈ (incoming i hi).support →
    x ≠ D.source i → x ≠ D.target i → Cone O r x
  outgoing_inside : ∀ a ha v hv x, x ∈ (outgoing a ha v hv).support → x ≠ v → Cone O a x

namespace IndexedRoutes
variable {G : Graph n} {O : RankedOrder n} {r : Fin n}
    {D : IncomingDemands G O r} {A : RootedSelection O r} (R : IndexedRoutes G O r D A)

/-- Traffic counts original demand indices, including different indices with
identical endpoints or identical selected walks. -/
noncomputable def pendingTraffic (a : Fin n) : Finset (DemandTag n) := by
  classical
  exact D.indices.filter (fun i => ∃ hi : i ∈ D.indices,
    ∃ x ∈ (R.incoming i hi).support, Cone O a x)

noncomputable def internalLoad (a : Fin n) : Finset (DemandTag n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ ha : i.1 ∈ A.nodes,
    ∃ hv : i.2 ∈ regionAdhesionSet G O i.1,
    O.rel i.1 a ∧ ∃ x ∈ (R.outgoing i.1 ha i.2 hv).support, Cone O a x)

def Bounded (k : Nat) : Prop := ∀ a ∈ A.nodes,
  (R.internalLoad a).card + (R.pendingTraffic a).card ≤ 2*k^3

theorem pendingTraffic_subset (a : Fin n) : R.pendingTraffic a ⊆ D.indices := by
  classical
  exact Finset.filter_subset _ _

/-- The two terms in the residual invariant are literally disjoint tag sets:
a pending origin is above the subtree root, and an internal origin is below. -/
theorem internal_pending_disjoint (a : Fin n) : Disjoint (R.internalLoad a) (R.pendingTraffic a) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hp
  obtain ⟨hbase,_,_⟩ := (Finset.mem_filter.mp hi).2
  have habove := D.above i (R.pendingTraffic_subset a hp)
  rcases A.inside i.1 hbase with hbelow | hbelow
  · exact O.irrefl r (O.trans hbelow habove)
  · exact O.irrefl r (hbelow.symm ▸ habove)

theorem bounded_union_iff (k : Nat) : R.Bounded k ↔
    ∀ a ∈ A.nodes, (R.internalLoad a ∪ R.pendingTraffic a).card ≤ 2*k^3 := by
  classical
  simp only [Bounded,Finset.card_union_of_disjoint (R.internal_pending_disjoint _)]

/-- At the top-level empty demand family, the residual invariant gives the
unconditional indexed load cap needed by the stable 5.10 API. -/
theorem bounded_load (k : Nat) (h : R.Bounded k) (a : Fin n) (ha : a ∈ A.nodes) :
    (R.internalLoad a).card ≤ 2*k^3 :=
  (Nat.le_add_right _ _).trans (h a ha)

end IndexedRoutes
end StackSorting.LowPathwidthParts
