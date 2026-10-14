import PrefixConePartition

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}
namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)

/-- The root contraction fiber is exactly the chosen prefix when all frontier
roots are selected and no other selected node lies inside the prefix. -/
theorem owner_root_iff_prefix (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (honly : ∀ x ∈ A.nodes, x ∈ Z → x = r)
    (hfront : ∀ z, Frontier (clippedParent O r) Z z → z ∈ A.nodes)
    (v : Fin n) (hv : Cone O r v) : (A.owner v hv).val = r ↔ v ∈ Z := by
  classical
  constructor
  · intro he
    by_contra hout
    obtain ⟨z,hz,hzv⟩ := outside_prefix_frontier O r Z hp v hv hout
    have hzr := A.owner_nearest v hv (hfront z hz) hzv
    rw [he] at hzr
    have hrz := (relative_frontier_cone O r Z hp z hz).1
    rcases hzr with hzr | hzr
    · exact O.irrefl r (O.trans hrz hzr)
    · exact O.irrefl r (hzr ▸ hrz)
  · intro hin
    apply honly _ (A.owner v hv).property
    exact relativePrefix_ancestor O r Z hp (A.inside _ (A.owner v hv).property)
      (A.owner_ancestor v hv) hin

/-- Consequently the root's literal contracted margin is the prefix's
original-vertex set, the vertex carrier used by the marginal BagPath adapter. -/
theorem contracted_root_margin_iff (G : Graph n) (Z : Finset (Fin n))
    (hp : RelativePrefix O r Z)
    (honly : ∀ x ∈ A.nodes, x ∈ Z → x = r)
    (hfront : ∀ z, Frontier (clippedParent O r) Z z → z ∈ A.nodes)
    (v : Fin n) :
    (v ∈ A.contractedBag G ⟨r,A.root_mem⟩ ∧ ¬ RegionAdhesion G O r v) ↔ v ∈ Z := by
  rw [A.contractedMargin_iff]
  constructor
  · rintro ⟨hv,he⟩
    exact (A.owner_root_iff_prefix Z hp honly hfront v hv).mp he
  · intro hv
    exact ⟨hp.2.2 v hv,(A.owner_root_iff_prefix Z hp honly hfront v (hp.2.2 v hv)).mpr hv⟩

end RootedSelection
end StackSorting.LowPathwidthParts
