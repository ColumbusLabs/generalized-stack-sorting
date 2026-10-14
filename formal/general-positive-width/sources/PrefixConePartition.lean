import ContractedRegions

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth
variable {n : Nat}

/-- Every unexposed descendant has a concrete first frontier ancestor,
constructed by walking toward the prefix along the actual parent. -/
theorem outside_prefix_frontier (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (v : Fin n)
    (hv : Cone O r v) (hout : v ∉ Z) :
    ∃ z, Frontier (clippedParent O r) Z z ∧ Cone O z v := by
  classical
  have hvr : v ≠ r := fun he => hout (he.symm ▸ hp.2.1)
  have hrv : O.rel r v := hv.resolve_right (Ne.symm hvr)
  by_cases hparent : O.parent v ∈ Z
  · exact ⟨v,⟨hout,by simpa [clippedParent,hvr] using hparent⟩,cone_refl O v⟩
  · obtain ⟨z,hz,hzparent⟩ := outside_prefix_frontier O r Z hp (O.parent v)
      (cone_parent O hrv) hparent
    exact ⟨z,hz,cone_trans O hzparent (Or.inl (O.parent_of_pred hrv).1)⟩
termination_by O.rank v
decreasing_by exact O.parent_rank_lt (O.parent_ne_of_pred hrv)

theorem frontier_antichain (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) {z w : Fin n}
    (hz : Frontier (clippedParent O r) Z z) (hw : Frontier (clippedParent O r) Z w)
    (hzw : Cone O z w) : z = w := by
  rcases hzw with hzw | hzw
  · have hzp := cone_parent O hzw
    have hrz := (relative_frontier_cone O r Z hp z hz).1
    have hwp := (relative_frontier_cone O r Z hp w hw).2.1
    exact (hz.1 (relativePrefix_ancestor O r Z hp (Or.inl hrz) hzp hwp)).elim
  · exact hzw

theorem cone_predecessors (O : RankedOrder n) {z w v : Fin n}
    (hz : Cone O z v) (hw : Cone O w v) : Cone O z w ∨ Cone O w z := by
  rcases hz with hz | hz
  · rcases hw with hw | hw
    · rcases O.predecessors hz hw with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl (hw.symm ▸ Or.inl hz)
  · exact Or.inr (hz.symm ▸ hw)

/-- Distinct literal boundary IDs have disjoint original components. -/
theorem frontier_cones_disjoint (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) {z w v : Fin n}
    (hz : Frontier (clippedParent O r) Z z) (hw : Frontier (clippedParent O r) Z w)
    (hzv : Cone O z v) (hwv : Cone O w v) : z = w := by
  rcases cone_predecessors O hzv hwv with h | h
  · exact frontier_antichain O r Z hp hz hw h
  · exact (frontier_antichain O r Z hp hw hz h).symm

/-- The recursion domains are a genuine partition of the unexposed nodes. -/
theorem prefix_partition (O : RankedOrder n) (r : Fin n)
    (Z : Finset (Fin n)) (hp : RelativePrefix O r Z) (v : Fin n) (hv : Cone O r v) :
    v ∈ Z ∨ ∃! z, Frontier (clippedParent O r) Z z ∧ Cone O z v := by
  classical
  by_cases hin : v ∈ Z
  · exact Or.inl hin
  · obtain ⟨z,hz,hzv⟩ := outside_prefix_frontier O r Z hp v hv hin
    exact Or.inr ⟨z,⟨hz,hzv⟩,fun w hw => frontier_cones_disjoint O r Z hp hw.1 hz hw.2 hzv⟩

end StackSorting.LowPathwidthParts
