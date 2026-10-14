import HyperpathTraversalEndpoints
import PrefixRoutingFamily

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat} {G : Graph n} {O : RankedOrder n} {r : Fin n}
    {Z : Finset (Fin n)} {s t : Fin n}

structure BoundaryPass (p : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t) (z : Fin n) where
  edge : ActiveEdge (CanonicalPrefixInc G O r Z)
  edge_id : edge.val = .inr z
  used : edge ∈ p.walk.edges

noncomputable def boundaryPass (p : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t)
    (z : Fin n) (h : Sum.inr z ∈ p.walk.edges.map Subtype.val) : BoundaryPass p z := by
  classical
  let hex := List.mem_map.mp h
  let e := Classical.choose hex
  exact ⟨e,(Classical.choose_spec hex).2,(Classical.choose_spec hex).1⟩

namespace BoundaryPass
variable {p : Path (ActiveIncidence (CanonicalPrefixInc G O r Z)) s t} {z : Fin n}
    (B : BoundaryPass p z)

noncomputable def before : Fin n := (p.walk.chooseTraversal B.edge B.used).before
noncomputable def after : Fin n := (p.walk.chooseTraversal B.edge B.used).after

theorem endpoints_in_adhesion : RegionAdhesion G O z B.before ∧ RegionAdhesion G O z B.after := by
  have h := p.walk.chooseTraversal_incident B.edge B.used
  have hbefore := h.1.1
  have hafter := h.2.1
  change PrefixHypertorsoInc G O r Z B.before B.edge.val at hbefore
  change PrefixHypertorsoInc G O r Z B.after B.edge.val at hafter
  rw [B.edge_id] at hbefore hafter
  exact ⟨hbefore.2,hafter.2⟩

/-- Every occurrence of this boundary edge has exactly the selected endpoints,
so the recursive replacement uses one consistent demand per original index. -/
theorem endpoints_exact {a b : Fin n} (h : (a,B.edge,b) ∈ p.walk.traversals) :
    a = B.before ∧ b = B.after :=
  p.walk.traversal_unique p.edges_nodup h (p.walk.chooseTraversal B.edge B.used).occurs

end BoundaryPass
end StackSorting.LowPathwidthParts
