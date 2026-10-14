import IndexedRoutingState
import ChildDemandExtraction
import SelectionPathwidthParts
import ChooseBoundedRoutingPrefix
import SelectedRegionAssembly

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

/-- Simultaneous output of the actual subtree construction. Its existence is
not assumed by the global theorem: the remaining induction must construct
all three of the selected nodes, original-edge routes and marginal bags. -/
structure SubtreeRoutingSolution (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (D : IncomingDemands G O r) (k : Nat) where
  selected : RootedSelection O r
  routes : IndexedRoutes G O r D selected
  bounded : routes.Bounded k
  parts : selected.PathwidthParts G (2*k+2)

/-- Recursive child data has concrete extracted demands, not a supplied
routing oracle on arbitrary endpoint pairs. -/
structure ChildRoutingSolutions (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (D : IncomingDemands G O r) (k : Nat) (Z : Finset (Fin n))
    (hp : RelativePrefix O r Z) (F : PrefixRoutingFamily G O r D Z) where
  child : ∀ z (hz : Frontier (clippedParent O r) Z z),
    SubtreeRoutingSolution G O z (F.childDemands z (relative_frontier_cone O r Z hp z hz).1) k

end StackSorting.LowPathwidthParts
