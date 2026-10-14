import MarginalEdgeCodes
import DecompositionBagColoring

namespace StackSorting.GraphWidth.MarginalA2
open FinitePort Nested
variable {n s t W : Nat} {G : Graph n} {S : RootedTree s} {T : RootedTree t}

/-- The fixed adhesion-separating coloring is constructed from the original
bounded decomposition and literal inherited-bag containment. The outer bags
are not assumed bounded or captured. -/
theorem exists_adhesionColoring (original : Decomposition G S) (D : Decomposition G T)
    (hb : original.BagBound W)
    (contained : ∀ y, ∃ x, ∀ v, outerAdhesion D y v → v∈original.bag x) :
    Nonempty (AdhesionColoring D W) := by
  obtain ⟨color,hcolor⟩ := exists_inherited_adhesion_coloring original hb (outerAdhesion D) contained
  refine ⟨⟨color,?_⟩⟩
  intro y u v hu hv he
  by_contra hne
  exact hcolor y u v hu hv hne he

#print axioms exists_adhesionColoring
end StackSorting.GraphWidth.MarginalA2
