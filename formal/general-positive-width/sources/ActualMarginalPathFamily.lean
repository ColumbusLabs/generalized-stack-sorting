import SelectionPathwidthParts
import LiteralMarginIntroduction
import MarginalBagPathTransport
import MarginalLocalGuidance

namespace StackSorting.LowPathwidthParts
open GraphWidth SameVertexForest ConnectedConeNormalization FinitePort
namespace RootedSelection
variable {n : Nat} {O : RankedOrder n} {r : Fin n} (A : RootedSelection O r)
noncomputable section
local instance familyDecidable : DecidablePred (fun x => x ∈ A.nodes) := Classical.decPred _

/-- The completed marginal's original-vocabulary adhesion is precisely the
old selected region adhesion. This direction suffices for exact edge coverage. -/
theorem outerAdhesion_region (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : Fin (Fintype.card A.Selected)) (v : Fin n)
    (h : Nested.outerAdhesion (A.contractedDecomposition G hall helim) i v) :
    RegionAdhesion G O (A.selectedLabel i).val v := by
  by_contra hn
  apply h.2
  apply (literal_margin_iff_introduction (A.contractedDecomposition G hall helim) i v).mp
  exact ⟨h.1,fun ha => hn ((A.actual_adhesion_iff G hall helim i v).mp ha)⟩

/-- The actual original vertex belonging to a numbered marginal lies in the
constructed nearest-selected-owner fiber, with no additional vertices. -/
theorem introduction_mem_margin (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (i : Fin (Fintype.card A.Selected)) (v : Fin n)
    (h : introductionNode (A.contractedDecomposition G hall helim) v = i) :
    v ∈ A.marginSet G (A.selectedLabel i) := by
  rw [A.mem_marginSet,A.contractedMargin_iff]
  exact ⟨hall v,(A.contracted_introduction_iff hall helim i v).mp h⟩

/-- Construct the ordered path word of the exact completed marginal from the
actual bag path. The numbering is a genuine bijection of its introduction fiber. -/
def actualMarginalWord (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    {k q : Nat} (F : A.PathwidthParts G (2*k+2))
    (i : Fin (Fintype.card A.Selected))
    (names : Fin q ≃ {v : Fin n // introductionNode (A.contractedDecomposition G hall helim) v = i}) :
    BiInterface.PathWord.Decomposition (MarginalA2.Local.graphOriginal
      (Nested.marginalGraph (A.contractedDecomposition G hall helim) i names)) (2*k+2) := by
  classical
  let f : Fin q → Fin n := fun x => (names x).val
  have inj : Function.Injective f := fun x y h => names.injective (Subtype.ext h)
  have inside : ∀ x, f x ∈ A.marginSet G (A.selectedLabel i) := fun x =>
    A.introduction_mem_margin G hall helim i (f x) (names x).property
  let D := pullbackBagPath (F.path (A.selectedLabel i)) f inj inside
  apply bagPathToPathWord D
  intro u v huv
  have edge : A.MarginalEdge G (A.selectedLabel i) (f u) (f v) := by
    rcases huv.2 with he | ⟨j,hj,hparent,hu,hv⟩
    · exact Or.inl he
    · have hp : A.contractedParent (A.selectedLabel j) = A.selectedLabel i := by
        rw [← A.selected_parent_exact,hparent]
      exact Or.inr ⟨A.selectedLabel j,A.selectedLabel_ne_root hj,hp,
        A.outerAdhesion_region G hall helim j (f u) hu,
        A.outerAdhesion_region G hall helim j (f v) hv⟩
  obtain ⟨j,hj,hu,hv⟩ := F.edge (A.selectedLabel i) (f u) (f v) (inside u) (inside v) edge
  exact ⟨j,hj,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩

/-- Exact A.2 interface, constructed from the recursively assembled concrete
margin bag paths. The `names` field is an equivalence, not a quotient or a
noninjective image; its path covers the actual child-adhesion completion graph. -/
def actualPathFamily (G : Graph n) (hall : ∀ v, Cone O r v)
    (helim : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (k : Nat) (F : A.PathwidthParts G (2*k+2)) :
    MarginalA2.Local.PathFamily (A.contractedDecomposition G hall helim) k := by
  classical
  let V := fun i => {v : Fin n // introductionNode (A.contractedDecomposition G hall helim) v = i}
  let names := fun i => (Fintype.equivFin (V i)).symm
  exact {
    vertices := fun i => Fintype.card (V i)
    names := names
    path := fun i => A.actualMarginalWord G hall helim F i (names i)
  }

end
end RootedSelection
#print axioms RootedSelection.actualMarginalWord
#print axioms RootedSelection.actualPathFamily
end StackSorting.LowPathwidthParts
