import ContractedRegions

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FiniteFlow.Hypergraph
variable {n : Nat}
namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)

noncomputable def marginSet (G : Graph n) (a : {x : Fin n // x ∈ A.nodes}) : Finset (Fin n) :=
  A.contractedBag G a \ regionAdhesionSet G O a.val

@[simp] theorem mem_marginSet (G : Graph n) (a : {x : Fin n // x ∈ A.nodes}) (v : Fin n) :
    v ∈ A.marginSet G a ↔ v ∈ A.contractedBag G a ∧ ¬ RegionAdhesion G O a.val v := by
  classical
  simp [marginSet]

/-- The literal marginal-edge condition before numbering its margin vertices.
Both original edges and actual immediate-child adhesion cliques are included. -/
def MarginalEdge (G : Graph n) (a : {x : Fin n // x ∈ A.nodes}) (u v : Fin n) : Prop :=
  G.Adj u v ∨ ∃ c : {x : Fin n // x ∈ A.nodes}, c.val ≠ r ∧
    A.contractedParent c = a ∧ RegionAdhesion G O c.val u ∧ RegionAdhesion G O c.val v

/-- Actual ordered bags and common-bag coverage for every literal marginal.
This is the simultaneous pathwidth payload returned by subtree induction. -/
structure PathwidthParts (G : Graph n) (bound : Nat) where
  path : ∀ a : {x : Fin n // x ∈ A.nodes}, BagPath (A.marginSet G a) bound
  edge : ∀ a u v, u ∈ A.marginSet G a → v ∈ A.marginSet G a → A.MarginalEdge G a u v →
    ∃ i, i ≤ (path a).last ∧ u ∈ (path a).bag i ∧ v ∈ (path a).bag i

end RootedSelection
end StackSorting.LowPathwidthParts
