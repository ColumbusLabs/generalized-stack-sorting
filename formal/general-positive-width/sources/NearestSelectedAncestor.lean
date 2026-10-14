import PrunedPrefixSeparation

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

structure RootedSelection (O : RankedOrder n) (r : Fin n) where
  nodes : Finset (Fin n)
  root_mem : r ∈ nodes
  inside : ∀ x ∈ nodes, Cone O r x

namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)

/-- The actual nearest selected ancestor, computed by climbing the original
parent. Termination uses the original strictly decreasing rank. -/
noncomputable def owner (v : Fin n) (hv : Cone O r v) : {x : Fin n // x ∈ A.nodes} := by
  classical
  exact if hx : v ∈ A.nodes then ⟨v,hx⟩ else
    let hn : v ≠ r := fun he => hx (he.symm ▸ A.root_mem)
    let hrv : O.rel r v := hv.resolve_right (Ne.symm hn)
    owner (O.parent v) (cone_parent O hrv)
termination_by O.rank v
decreasing_by exact O.parent_rank_lt (O.parent_ne_of_pred hrv)

theorem owner_selected (v : Fin n) (hv : Cone O r v) (hx : v ∈ A.nodes) :
    (A.owner v hv).val = v := by
  simp [owner,hx]

theorem owner_parent (v : Fin n) (hv : Cone O r v) (hx : v ∉ A.nodes)
    (hrv : O.rel r v) :
    A.owner v hv = A.owner (O.parent v) (cone_parent O hrv) := by
  conv_lhs => rw [owner]
  simp only [dite_eq_right hx]

theorem owner_ancestor (v : Fin n) (hv : Cone O r v) : Cone O (A.owner v hv).val v := by
  by_cases hx : v ∈ A.nodes
  · rw [A.owner_selected v hv hx]
    exact cone_refl O v
  · have hn : v ≠ r := fun he => hx (he.symm ▸ A.root_mem)
    have hrv : O.rel r v := hv.resolve_right (Ne.symm hn)
    rw [A.owner_parent v hv hx hrv]
    exact cone_trans O (owner_ancestor (O.parent v) (cone_parent O hrv))
      (Or.inl (O.parent_of_pred hrv).1)
termination_by O.rank v
decreasing_by exact O.parent_rank_lt (O.parent_ne_of_pred hrv)

/-- Every selected ancestor lies above the constructed owner. -/
theorem owner_nearest (v : Fin n) (hv : Cone O r v) {x : Fin n}
    (hx : x ∈ A.nodes) (hxv : Cone O x v) : Cone O x (A.owner v hv).val := by
  by_cases hsel : v ∈ A.nodes
  · rw [A.owner_selected v hv hsel]
    exact hxv
  · have hn : v ≠ r := fun he => hsel (he.symm ▸ A.root_mem)
    have hrv : O.rel r v := hv.resolve_right (Ne.symm hn)
    have hne : x ≠ v := fun he => hsel (he ▸ hx)
    have hrel : O.rel x v := hxv.resolve_right hne
    rw [A.owner_parent v hv hsel hrv]
    exact owner_nearest (O.parent v) (cone_parent O hrv) hx (cone_parent O hrel)
termination_by O.rank v
decreasing_by exact O.parent_rank_lt (O.parent_ne_of_pred hrv)

end RootedSelection

theorem cone_antisymm (O : RankedOrder n) {x y : Fin n} (hxy : Cone O x y) (hyx : Cone O y x) : x = y := by
  rcases hxy with hxy | he
  · rcases hyx with hyx | he
    · exact (O.irrefl x (O.trans hxy hyx)).elim
    · exact he.symm
  · exact he

namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)

/-- Fibers of the nearest-selected-ancestor map are actual connected tree
regions: every node between an owner and an assigned descendant has that owner. -/
theorem owner_interval (v : Fin n) (hv : Cone O r v) {u : Fin n}
    (hau : Cone O (A.owner v hv).val u) (huv : Cone O u v) :
    A.owner u (cone_trans O (A.inside _ (A.owner v hv).property) hau) = A.owner v hv := by
  let hu := cone_trans O (A.inside _ (A.owner v hv).property) hau
  apply Subtype.ext
  apply cone_antisymm O
  · exact A.owner_nearest v hv (A.owner u hu).property
      (cone_trans O (A.owner_ancestor u hu) huv)
  · exact A.owner_nearest u hu (A.owner v hv).property hau

end RootedSelection
end StackSorting.LowPathwidthParts
