import PathwidthGuidanceExistence
import RealizedGuidedDecomposition

namespace StackSorting.BiInterface.PathWord
open GuidedPathwidth
universe u
variable {V : Type u} {k : Nat}

/-- The final bounded-guidance endpoint uses actual selected vertex sets,
actual original-edge acyclic forests, actual roots and finite graph walks. -/
theorem exists_forest_guidance_of_path_decomposition [DecidableEq V]
    (G : Original V) (D : Decomposition G k) :
    ∃ E : ForestGuidedDecomposition G.simple Set.univ (pathwidthPalette k),
      E.decomposition.forest.IsTree := by
  obtain ⟨E,hE⟩ := exists_tree_guided_path_decomposition G D
  exact ⟨E.realize,hE⟩

/-- The constructed real index tree also has an explicit parameter-only bag
bound, derived from unique roots in each actual forest color. -/
theorem exists_bounded_forest_guidance_of_path_decomposition [DecidableEq V]
    (G : Original V) (D : Decomposition G k) :
    ∃ E : ForestGuidedDecomposition G.simple Set.univ (pathwidthPalette k),
      E.decomposition.forest.IsTree ∧
      ∀ a, Nat.card (E.decomposition.bag a) ≤ pathwidthPalette k := by
  obtain ⟨E,hE⟩ := exists_forest_guidance_of_path_decomposition G D
  exact ⟨E,hE,E.bag_card_le⟩

#print axioms exists_forest_guidance_of_path_decomposition
#print axioms exists_bounded_forest_guidance_of_path_decomposition
end StackSorting.BiInterface.PathWord
