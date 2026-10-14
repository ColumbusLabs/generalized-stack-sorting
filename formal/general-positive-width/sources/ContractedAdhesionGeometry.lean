import ContractedAncestry
import AdhesionGeometry

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FinitePort
variable {n : Nat}
namespace RootedSelection
variable {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)
noncomputable section
local instance adhesionDecidable : DecidablePred (fun x => x ∈ A.nodes) := Classical.decPred _

theorem root_regionAdhesion_empty (G : Graph n) (hall : ∀ v, Cone O r v) (u : Fin n) :
    ¬ RegionAdhesion G O r u := by
  intro hu
  have hparent : O.rel (O.parent r) r := O.parent_rel hu.1
  rcases hall (O.parent r) with hr | hr
  · exact O.irrefl r (O.trans hr hparent)
  · rw [← hr] at hparent
    exact O.irrefl r hparent

/-- Equality with the original selected adhesion gives the precise bounded-bag
containment required by the inherited adhesion coloring theorem. -/
theorem actual_adhesion_iff (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : Fin (Fintype.card A.Selected)) (u : Fin n) :
    u ∈ AdhesionGuidance.adhesion (A.contractedDecomposition G hall helim) i ↔
      RegionAdhesion G O (A.selectedLabel i).val u := by
  by_cases hi : i.val = 0
  · have he := congrArg Subtype.val (A.selectedLabel_root i hi)
    simp only [AdhesionGuidance.adhesion,Set.mem_ofPred_eq,hi,ne_eq,not_true_eq_false,false_and]
    rw [he]
    exact ⟨False.elim,fun h => root_regionAdhesion_empty G hall u h⟩
  · change (i.val ≠ 0 ∧ u ∈ (A.contractedBag G (A.selectedLabel i)).toList ∧
      u ∈ (A.contractedBag G (A.selectedLabel (A.selectedTree.parent i))).toList) ↔ _
    simp only [Finset.mem_toList,A.selected_parent_exact]
    constructor
    · intro h
      exact (A.contracted_intersection_iff G _ (A.selectedLabel_ne_root hi) u).mp h.2
    · intro h
      exact ⟨hi,(A.contracted_intersection_iff G _ (A.selectedLabel_ne_root hi) u).mpr h⟩

theorem actual_adhesion_in_original_bag (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : Fin (Fintype.card A.Selected)) :
    AdhesionGuidance.adhesion (A.contractedDecomposition G hall helim) i ⊆
      ↑(regionBagSet G O (A.selectedLabel i).val) := by
  intro u hu
  exact (mem_regionBagSet G O _ _).mpr ((A.actual_adhesion_iff G hall helim i u).mp hu).2.1

/-- The stable 5.10 literal component agrees with the original connected cone. -/
theorem actual_component_iff (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : Fin (Fintype.card A.Selected)) (u : Fin n) :
    u ∈ AdhesionGuidance.component (A.contractedDecomposition G hall helim) i ↔
      Cone O (A.selectedLabel i).val u := by
  change ((∃ j, Ancestor A.selectedTree i j ∧
    u ∈ (A.contractedBag G (A.selectedLabel j)).toList) ∧
    u ∉ AdhesionGuidance.adhesion (A.contractedDecomposition G hall helim) i) ↔ _
  simp only [Finset.mem_toList,A.actual_adhesion_iff]
  rw [← A.contractedComponent_iff G (A.selectedLabel i) u]
  constructor
  · rintro ⟨⟨j,hij,hu⟩,hn⟩
    exact ⟨⟨A.selectedLabel j,A.selected_ancestor_cone hij,hu⟩,hn⟩
  · rintro ⟨⟨b,hib,hu⟩,hn⟩
    refine ⟨⟨A.selectedIndex b,?_,?_⟩,hn⟩
    · exact (A.selected_ancestor_iff i (A.selectedIndex b)).mpr (by simpa using hib)
    · simpa using hu

/-- The selected original vertex is a concrete representative in the actual
contracted margin; no nonempty-margin choice is left as a premise. -/
theorem actual_margin_representative (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : Fin (Fintype.card A.Selected)) :
    (A.selectedLabel i).val ∈ AdhesionGuidance.margin (A.contractedDecomposition G hall helim) i := by
  refine ⟨?_,?_⟩
  · change (A.selectedLabel i).val ∈ (A.contractedBag G (A.selectedLabel i)).toList
    apply Finset.mem_toList.mpr
    exact A.original_bag_subset G _ ((mem_regionBagSet G O _ _).mpr (Or.inl rfl))
  · rw [A.actual_adhesion_iff]
    exact cone_disjoint_adhesion G O (cone_refl O _)

end
end RootedSelection
end StackSorting.LowPathwidthParts
