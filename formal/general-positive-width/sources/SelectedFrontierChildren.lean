import SelectedPrefixFibers

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}
namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)

/-- The immediate contracted children of the current root are exactly the
literal prefix frontier IDs, preserving parallel adhesion identifiers. -/
theorem root_child_iff_frontier (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (honly : ∀ x ∈ A.nodes, x ∈ Z → x = r)
    (hfront : ∀ z, Frontier (clippedParent O r) Z z → z ∈ A.nodes)
    (a : {x : Fin n // x ∈ A.nodes}) (har : a.val ≠ r) :
    (A.contractedParent a).val = r ↔ Frontier (clippedParent O r) Z a.val := by
  classical
  have hra := (A.inside a.val a.property).resolve_right (Ne.symm har)
  constructor
  · intro he
    have haout : a.val ∉ Z := fun h => har (honly a.val a.property h)
    obtain ⟨z,hz,hza⟩ := outside_prefix_frontier O r Z hp a.val (A.inside _ a.property) haout
    by_cases hzaeq : z = a.val
    · exact hzaeq ▸ hz
    · have hzrel := hza.resolve_right hzaeq
      have hnear := A.owner_nearest (O.parent a.val) (cone_parent O hra) (hfront z hz)
        (cone_parent O hzrel)
      have he' : (A.owner (O.parent a.val) (cone_parent O hra)).val = r := by
        simpa only [A.contractedParent_eq a har hra] using he
      rw [he'] at hnear
      have hrz := (relative_frontier_cone O r Z hp z hz).1
      rcases hnear with hnear | hnear
      · exact (O.irrefl r (O.trans hrz hnear)).elim
      · exact (O.irrefl r (hnear ▸ hrz)).elim
  · intro ha
    rw [A.contractedParent_eq a har hra]
    exact (A.owner_root_iff_prefix Z hp honly hfront (O.parent a.val) (cone_parent O hra)).mpr
      (relative_frontier_cone O r Z hp a.val ha).2.1

end RootedSelection
end StackSorting.LowPathwidthParts
