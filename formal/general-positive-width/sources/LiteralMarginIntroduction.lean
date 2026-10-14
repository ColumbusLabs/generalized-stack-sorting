import ContractedAdhesionGeometry

namespace StackSorting.LowPathwidthParts
open GraphWidth FinitePort SameVertexForest ConnectedConeNormalization

/-- The literal bag-minus-adhesion margin is exactly the introduction fiber
used by the independently constructed marginal graph encoding. -/
theorem literal_margin_iff_introduction {n t : Nat} {G : Graph n} {T : RootedTree t}
    (D : Decomposition G T) (i : Fin t) (v : Fin n) :
    v ∈ AdhesionGuidance.margin D i ↔ introductionNode D v = i := by
  constructor
  · intro h
    exact TreeAncestry.antisymm (introduction_ancestor D h.1)
      ((AdhesionGuidance.component_iff D i v).mp (AdhesionGuidance.margin_component D h))
  · intro he
    refine ⟨he ▸ (introduction_spec D v).1,?_⟩
    intro ha
    exact (AdhesionGuidance.adhesion_introduction D ha).2 he

noncomputable section
namespace RootedSelection
variable {n : Nat} {G : Graph n} {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)

local instance marginIntroDecidable : DecidablePred (fun x => x ∈ A.nodes) := Classical.decPred _

/-- The actual introduction-node fiber of the numbered contraction is exactly
its constructed nearest-selected-owner fiber on original vertices. -/
theorem contracted_introduction_iff (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : Fin (Fintype.card A.Selected)) (v : Fin n) :
    introductionNode (A.contractedDecomposition G hall helim) v = i ↔
      (A.owner v (hall v)).val = (A.selectedLabel i).val := by
  classical
  rw [← literal_margin_iff_introduction]
  change (v ∈ (A.contractedBag G (A.selectedLabel i)).toList ∧
    v ∉ AdhesionGuidance.adhesion (A.contractedDecomposition G hall helim) i) ↔ _
  rw [Finset.mem_toList,A.actual_adhesion_iff,A.contractedMargin_iff]
  constructor
  · rintro ⟨hv,he⟩
    exact he
  · intro he
    exact ⟨hall v,he⟩

end RootedSelection
end
end StackSorting.LowPathwidthParts
