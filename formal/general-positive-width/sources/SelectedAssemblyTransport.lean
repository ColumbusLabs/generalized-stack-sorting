import SelectedRegionAssembly

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

theorem assembled_ancestor_child (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z) {a q : Fin n}
    (hza : Cone O z a) (hq : q ∈ (assembleSelection O r Z hp children).nodes)
    (hqa : O.rel q a) (hqr : q ≠ r) : q ∈ (children z hz).nodes := by
  rcases (assembled_mem O r Z hp children q).mp hq with he | ⟨w,hw,hq⟩
  · exact (hqr he).elim
  · have hwa := cone_trans O ((children w hw).inside q hq) (Or.inl hqa)
    have he := frontier_cones_disjoint O r Z hp hz hw hza hwa
    subst w
    exact hq

/-- Every recursive child's actual union bag is unchanged by assembly. -/
theorem assembled_bag_child (G : Graph n) (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (a : {x : Fin n // x ∈ (children z hz).nodes}) :
    (assembleSelection O r Z hp children).contractedBag G
      ⟨a.val,(assembled_mem O r Z hp children a.val).mpr (Or.inr ⟨z,hz,a.property⟩)⟩ =
      (children z hz).contractedBag G a := by
  classical
  let A := assembleSelection O r Z hp children
  let C := children z hz
  have hrz : Cone O r z := Or.inl (relative_frontier_cone O r Z hp z hz).1
  ext u
  constructor
  · intro hu
    obtain ⟨v,hv,he,hvu⟩ := (A.mem_contractedBag G _ u).mp hu
    have hav : Cone O a.val v := he ▸ A.owner_ancestor v hv
    have hzv := cone_trans O (C.inside a.val a.property) hav
    have ho := assembled_owner_child O r Z hp children z hz v hzv
    exact (C.mem_contractedBag G a u).mpr ⟨v,hzv,ho.symm.trans he,hvu⟩
  · intro hu
    obtain ⟨v,hv,he,hvu⟩ := (C.mem_contractedBag G a u).mp hu
    have ho := assembled_owner_child O r Z hp children z hz v hv
    exact (A.mem_contractedBag G _ u).mpr ⟨v,cone_trans O hrz hv,ho.trans he,hvu⟩

/-- Nonroot parents inside a recursive child's selected tree are preserved
literally; the child root alone acquires its new outside parent. -/
theorem assembled_parent_child (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z)
    (a : {x : Fin n // x ∈ (children z hz).nodes}) (haz : a.val ≠ z) :
    ((assembleSelection O r Z hp children).contractedParent
      ⟨a.val,(assembled_mem O r Z hp children a.val).mpr (Or.inr ⟨z,hz,a.property⟩)⟩).val =
      ((children z hz).contractedParent a).val := by
  let A := assembleSelection O r Z hp children
  let C := children z hz
  have hza := (C.inside a.val a.property).resolve_right (Ne.symm haz)
  have hra := O.trans (relative_frontier_cone O r Z hp z hz).1 hza
  have har : a.val ≠ r := fun he => O.irrefl r (by simpa only [he] using hra)
  rw [A.contractedParent_eq _ har hra,C.contractedParent_eq a haz hza]
  exact assembled_owner_child O r Z hp children z hz (O.parent a.val) (cone_parent O hza)

end StackSorting.LowPathwidthParts
