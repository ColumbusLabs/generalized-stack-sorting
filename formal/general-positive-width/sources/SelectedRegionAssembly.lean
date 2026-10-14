import SelectedPrefixFibers

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

/-- Assemble the selected root and the independently constructed selections
inside the pairwise disjoint frontier cones. -/
noncomputable def assembleSelection (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z) :
    RootedSelection O r := by
  classical
  exact {
    nodes := Finset.univ.filter (fun x => x = r ∨ ∃ z hz, x ∈ (children z hz).nodes)
    root_mem := by simp
    inside := by
      intro x hx
      rcases (Finset.mem_filter.mp hx).2 with he | ⟨z,hz,hx⟩
      · exact Or.inr he.symm
      · exact cone_trans O (Or.inl (relative_frontier_cone O r Z hp z hz).1)
          ((children z hz).inside x hx)
  }

theorem assembled_mem (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z) (x : Fin n) :
    x ∈ (assembleSelection O r Z hp children).nodes ↔
      x = r ∨ ∃ z hz, x ∈ (children z hz).nodes := by
  classical
  simp [assembleSelection]

theorem assembled_frontier (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z) :
    z ∈ (assembleSelection O r Z hp children).nodes :=
  (assembled_mem O r Z hp children z).mpr (Or.inr ⟨z,hz,(children z hz).root_mem⟩)

theorem assembled_only_root (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (x : Fin n) (hx : x ∈ (assembleSelection O r Z hp children).nodes) (hxZ : x ∈ Z) : x = r := by
  rcases (assembled_mem O r Z hp children x).mp hx with he | ⟨z,hz,hx⟩
  · exact he
  · exact (hz.1 (relativePrefix_ancestor O r Z hp
      (Or.inl (relative_frontier_cone O r Z hp z hz).1)
      ((children z hz).inside x hx) hxZ)).elim

/-- Inside one frontier cone, assembled selected nodes are exactly the
selected nodes of that recursive child, with no cross-child identifications. -/
theorem assembled_mem_child_iff (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z) (x : Fin n) (hzx : Cone O z x) :
    x ∈ (assembleSelection O r Z hp children).nodes ↔ x ∈ (children z hz).nodes := by
  constructor
  · intro hx
    rcases (assembled_mem O r Z hp children x).mp hx with he | ⟨w,hw,hx⟩
    · have hrz := (relative_frontier_cone O r Z hp z hz).1
      rw [he] at hzx
      rcases hzx with hzx | hzx
      · exact (O.irrefl r (O.trans hrz hzx)).elim
      · exact (O.irrefl r (hzx ▸ hrz)).elim
    · have hezw := frontier_cones_disjoint O r Z hp hz hw hzx ((children w hw).inside x hx)
      subst w
      exact hx
  · intro hx
    exact (assembled_mem O r Z hp children x).mpr (Or.inr ⟨z,hz,hx⟩)

/-- The actual nearest-selected assignment is unchanged within a recursively
assembled child. This transports its bags and pathwidth certificates. -/
theorem assembled_owner_child (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z)
    (children : ∀ z, Frontier (clippedParent O r) Z z → RootedSelection O z)
    (z : Fin n) (hz : Frontier (clippedParent O r) Z z) (v : Fin n) (hzv : Cone O z v) :
    ((assembleSelection O r Z hp children).owner v
      (cone_trans O (Or.inl (relative_frontier_cone O r Z hp z hz).1) hzv)).val =
      ((children z hz).owner v hzv).val := by
  let A := assembleSelection O r Z hp children
  let C := children z hz
  let hv := cone_trans O (Or.inl (relative_frontier_cone O r Z hp z hz).1) hzv
  have hzglobal := assembled_frontier O r Z hp children z hz
  have hzowner : Cone O z (A.owner v hv).val := A.owner_nearest v hv hzglobal hzv
  apply cone_antisymm O
  · exact C.owner_nearest v hzv
      ((assembled_mem_child_iff O r Z hp children z hz _ hzowner).mp (A.owner v hv).property)
      (A.owner_ancestor v hv)
  · exact A.owner_nearest v hv
      ((assembled_mem O r Z hp children _).mpr (Or.inr ⟨z,hz,(C.owner v hzv).property⟩))
      (C.owner_ancestor v hzv)

end StackSorting.LowPathwidthParts
