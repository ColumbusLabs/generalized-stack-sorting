import PrefixAvoidingRoutes

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}

/-- Tags are original (base,target) pairs. Equal traversal endpoint pairs do
not identify tags from different origins. -/
abbrev DemandTag (n : Nat) := Fin n × Fin n

structure IncomingDemands (G : Graph n) (O : RankedOrder n) (r : Fin n) where
  indices : Finset (DemandTag n)
  source : DemandTag n → Fin n
  target : DemandTag n → Fin n
  endpoints : ∀ i ∈ indices, RegionAdhesion G O r (source i) ∧ RegionAdhesion G O r (target i)
  above : ∀ i ∈ indices, O.rel i.1 r

namespace IncomingDemands
variable {G : Graph n} {O : RankedOrder n} {r : Fin n}
    (D : IncomingDemands G O r)

noncomputable def newIndices (_D : IncomingDemands G O r) : Finset (DemandTag n) := {r} ×ˢ regionAdhesionSet G O r
noncomputable def extendedIndices : Finset (DemandTag n) := D.indices ∪ D.newIndices

theorem disjoint_new : Disjoint D.indices D.newIndices := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have he : i.1 = r := Finset.mem_singleton.mp (Finset.mem_product.mp hj).1
  exact O.irrefl r (he ▸ D.above i hi)

theorem newIndices_card : D.newIndices.card = (regionAdhesionSet G O r).card := by
  classical
  simp [newIndices]

theorem extendedIndices_card : D.extendedIndices.card =
    D.indices.card + (regionAdhesionSet G O r).card := by
  classical
  rw [extendedIndices,Finset.card_union_of_disjoint D.disjoint_new,D.newIndices_card]

/-- Every tag forwarded to a proper descendant has its genuine origin
strictly above that descendant, including tags just created at this root. -/
theorem extended_above {z : Fin n} (hz : O.rel r z) {i : DemandTag n}
    (hi : i ∈ D.extendedIndices) : O.rel i.1 z := by
  classical
  rcases Finset.mem_union.mp hi with hi | hi
  · exact O.trans (D.above i hi) hz
  · have he : i.1 = r := Finset.mem_singleton.mp (Finset.mem_product.mp hi).1
    exact he.symm ▸ hz

/-- All nonspecial demands can be routed on the already chosen prefix.
The distinguished balanced fiber will subsequently replace some of these
paths with the two constructed 5.2 paths. -/
theorem exists_default_routes
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (Z : Finset (Fin n)) (hZ : RelativePrefix O r Z) :
    (∀ i ∈ D.indices, ∃ p : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) (D.source i) (D.target i),
      ∀ x ∈ p.walk.vertices, rootAllowed G O r (D.source i) (D.target i) x) ∧
    (∀ v ∈ regionAdhesionSet G O r, ∃ p : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) r v,
      ∀ x ∈ p.walk.vertices, rootAllowed G O r r v x) := by
  constructor
  · intro i hi
    exact exists_prefix_avoiding_route G O helim cones r Z hZ (D.source i) (D.target i)
      (D.endpoints i hi).1.2.1 (D.endpoints i hi).2.2.1
  · intro v hv
    exact exists_prefix_avoiding_route G O helim cones r Z hZ r v (Or.inl rfl)
      ((mem_regionAdhesionSet G O r v).mp hv).2.1

end IncomingDemands
end StackSorting.LowPathwidthParts
