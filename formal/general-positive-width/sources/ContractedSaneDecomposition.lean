import SuppliedLowPathwidthParts
import MultiMarginGeometry

/-!
The actual selected-node contraction is sane. This packages the already
constructed original-graph components and adhesion neighbors into the exact
multi-margin C.2 interface, without a supplied saneness witness.
-/
namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization PrefixGrowth FinitePort
open GraphWidth.Nested
variable {n : Nat} {G : Graph n} {O : RankedOrder n} {r : Fin n}

namespace RootedSelection
noncomputable section
variable (A : RootedSelection O r)
local instance saneDecidable : DecidablePred (fun x => x ∈ A.nodes) := Classical.decPred _

/-- The C.2 introduction component is exactly the original selected-root cone. -/
theorem contracted_introduction_component_iff
    (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : Fin (Fintype.card A.Selected)) (u : Fin n) :
    IntroductionComponent (A.contractedDecomposition G hall helim) i u ↔
      Cone O (A.selectedLabel i).val u := by
  exact (AdhesionGuidance.component_iff _ i u).symm.trans
    (A.actual_component_iff G hall helim i u)

/-- Contraction preserves genuine original-graph saneness, including a
neighbor for every actual adhesion vertex, rather than just a bag certificate. -/
theorem contracted_sane
    (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (cones : ∀ v u, Cone O v u → Walk G.Adj (Cone O v) v u) :
    MultiMargin.Sane (A.contractedDecomposition G hall helim) := by
  let D := A.contractedDecomposition G hall helim
  refine ⟨?_,?_,?_⟩
  · intro i
    exact ⟨(A.selectedLabel i).val,
      (literal_margin_iff_introduction D i _).mp
        (A.actual_margin_representative G hall helim i)⟩
  · intro i u v hu hv
    have hu' := (A.contracted_introduction_component_iff hall helim i u).mp hu
    have hv' := (A.contracted_introduction_component_iff hall helim i v).mp hv
    exact (((cones _ _ hu').reverse G.symm).trans (cones _ _ hv')).mono
      (fun w hw => (A.contracted_introduction_component_iff hall helim i w).mpr hw)
  · intro i u hu
    have ha : u ∈ AdhesionGuidance.adhesion D i :=
      (MultiMargin.adhesion_iff D i u).mpr hu
    have ha' := (A.actual_adhesion_iff G hall helim i u).mp ha
    obtain ⟨w,hw,he⟩ := adhesion_component_neighbor G O ha'
    exact ⟨w,(A.contracted_introduction_component_iff hall helim i w).mpr
      ((bagComponent_iff G O _ w).mp hw),he⟩

end
end RootedSelection
#print axioms RootedSelection.contracted_sane
end StackSorting.LowPathwidthParts
