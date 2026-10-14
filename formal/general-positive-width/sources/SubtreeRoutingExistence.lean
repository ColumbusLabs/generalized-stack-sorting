import AssembledRoutingLoad
import AssembledMarginalPaths
import ConeInduction

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

/-- Actual finite induction constructs the selected decomposition regions,
original-edge walks with indexed cubic load, and all concrete marginal bag
paths together. The recursive demand records are extracted from used boundary
traversals, and no routing or pathwidth existence oracle is a premise. -/
theorem exists_subtree_routing_solution (G : Graph n) (O : RankedOrder n)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → GraphWidth.Walk G.Adj (Cone O v) v u)
    (k : Nat) (width : ∀ z, (regionBagSet G O z).card ≤ k+1) :
    ∀ r (D : IncomingDemands G O r), D.indices.card ≤ 2*k^3 →
      Nonempty (SubtreeRoutingSolution G O r D k) := by
  classical
  refine cone_induction O (fun r => ∀ D : IncomingDemands G O r,
    D.indices.card ≤ 2*k^3 → Nonempty (SubtreeRoutingSolution G O r D k)) ?_
  intro r ih D hcap
  obtain ⟨Z,hp,F,hF,hsmall⟩ := exists_bounded_routing_prefix G O helim cones k width r D hcap
  let C : ChildRoutingSolutions G O r D k Z hp F := {
    child := fun z hz => Classical.choice (ih z (relative_frontier_cone O r Z hp z hz).1
      (F.childDemands z (relative_frontier_cone O r Z hp z hz).1)
      (F.childDemands_cap k hF z (relative_frontier_cone O r Z hp z hz).1))
  }
  exact ⟨{
    selected := C.assembledSelection
    routes := C.assembledRoutes
    bounded := C.assembled_bounded hcap
    parts := assemblePathwidthParts G O cones r k Z hp hsmall
      (fun z hz => (C.child z hz).selected) (fun z hz => (C.child z hz).parts)
  }⟩

end StackSorting.LowPathwidthParts
