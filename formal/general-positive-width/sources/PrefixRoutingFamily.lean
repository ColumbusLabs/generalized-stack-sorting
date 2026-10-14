import IndexedBoundaryTraffic
import EndpointPathTransport

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

/-- The actual initial hyperpaths used before the recursive replacements.
The bound counts every pending origin and every new adhesion target. -/
structure PrefixRoutingFamily (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (D : IncomingDemands G O r) (Z : Finset (Fin n)) where
  pending : ∀ i ∈ D.indices, Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) (D.source i) (D.target i)
  fresh : ∀ v ∈ regionAdhesionSet G O r, Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) r v
  pending_allowed : ∀ i hi x, x ∈ (pending i hi).walk.vertices → rootAllowed G O r (D.source i) (D.target i) x
  fresh_allowed : ∀ v hv x, x ∈ (fresh v hv).walk.vertices → rootAllowed G O r r v x

namespace PrefixRoutingFamily
variable {G : Graph n} {O : RankedOrder n} {r : Fin n} {D : IncomingDemands G O r}
    {Z : Finset (Fin n)} (R : PrefixRoutingFamily G O r D Z)

noncomputable def pendingUses (z : Fin n) : Finset (DemandTag n) := by
  classical
  exact D.indices.filter (fun i => ∃ hi : i ∈ D.indices,
    Sum.inr z ∈ (R.pending i hi).walk.edges.map Subtype.val)

noncomputable def freshUses (z : Fin n) : Finset (Fin n) := by
  classical
  exact (regionAdhesionSet G O r).filter (fun v => ∃ hv : v ∈ regionAdhesionSet G O r,
    Sum.inr z ∈ (R.fresh v hv).walk.edges.map Subtype.val)

def Bounded (k : Nat) : Prop := ∀ z,
  (R.pendingUses z).card + (R.freshUses z).card ≤ 2*k^3

theorem freshUses_bound (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1) (z : Fin n) :
    (R.freshUses z).card ≤ k := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (regionAdhesion_card_le G O k width r)

end PrefixRoutingFamily

/-- Forgetting subtype proofs retains each original boundary identifier;
therefore the two actual separating paths cannot share a raw boundary ID. -/
theorem raw_boundary_separate {G : Graph n} {O : RankedOrder n} {r s t : Fin n}
    {Z : Finset (Fin n)}
    (p q : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t)
    (hshared : ∀ e, e ∈ p.walk.edges → e ∈ q.walk.edges → IsOriginal e.val)
    (z : Fin n) :
    ¬ (Sum.inr z ∈ p.walk.edges.map Subtype.val ∧ Sum.inr z ∈ q.walk.edges.map Subtype.val) := by
  rintro ⟨hp,hq⟩
  obtain ⟨e,he,hez⟩ := List.mem_map.mp hp
  obtain ⟨f,hf,hfz⟩ := List.mem_map.mp hq
  have hef : e = f := Subtype.ext (hez.trans hfz.symm)
  exact canonical_boundary_separate p q hshared e hez ⟨he,hef.symm ▸ hf⟩

/-- Default actual routes exist on every genuine prefix. Their two prescribed
fiber halves are replaced by the separating paths in the next construction. -/
noncomputable def defaultPrefixRoutes (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (r : Fin n) (D : IncomingDemands G O r) (Z : Finset (Fin n)) (hZ : RelativePrefix O r Z) :
    PrefixRoutingFamily G O r D Z := by
  classical
  have routes := D.exists_default_routes helim cones Z hZ
  exact {
    pending := fun i hi => Classical.choose (routes.1 i hi)
    fresh := fun v hv => Classical.choose (routes.2 v hv)
    pending_allowed := fun i hi => Classical.choose_spec (routes.1 i hi)
    fresh_allowed := fun v hv => Classical.choose_spec (routes.2 v hv)
  }

end StackSorting.LowPathwidthParts
