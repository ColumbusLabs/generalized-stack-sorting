import PrefixConePartition
import IndexedRoutingDemands

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

theorem frontier_component_avoids_visible (G : Graph n) (O : RankedOrder n)
    (r : Fin n) (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z) {v : Fin n}
    (hv : v ∈ prefixVertices G O r Z) : ¬ Cone O z v := by
  rintro (h | h)
  · exact frontier_no_visible_descendant G O r Z hp z hz hv h
  · exact frontier_not_visible G O r Z hp z hz (h.symm ▸ hv)

/-- The precise support inclusion required from the constructed spliced walk.
Each hidden support vertex is witnessed in the same-index recursive route,
inside its actual frontier component. -/
def SplicedSupport (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n))
    (childSupport : ∀ z, Frontier (clippedParent O r) Z z → DemandTag n → Fin n → Prop)
    (i : DemandTag n) (v : Fin n) : Prop :=
  v ∈ prefixVertices G O r Z ∨ ∃ z hz, Cone O z v ∧ childSupport z hz i v

/-- A spliced path can hit a descendant component only through that unique
child's same-index route. This is the identity-tag injection behind the
additive residual-budget induction. -/
theorem spliced_support_child (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (childSupport : ∀ z, Frontier (clippedParent O r) Z z → DemandTag n → Fin n → Prop)
    (i : DemandTag n) (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    {v : Fin n} (hsupport : SplicedSupport G O r Z childSupport i v)
    (hzv : Cone O z v) : childSupport z hz i v := by
  rcases hsupport with hv | ⟨w,hw,hwv,hroute⟩
  · exact (frontier_component_avoids_visible G O r Z hp z hz hv hzv).elim
  · have he := frontier_cones_disjoint O r Z hp hz hw hzv hwv
    subst w
    exact hroute

end StackSorting.LowPathwidthParts
