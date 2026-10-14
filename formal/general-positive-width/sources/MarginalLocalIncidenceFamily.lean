import MarginalLocalGuidance
import GenericGuidanceFormula
import OwnerParameterMerge

/-! Family-level X/F/R merging is by disjoint owner, with exact restriction.
This is only the guidance tuple; the additional captured-link selection sets
must be built by the generic local extraction stage, still a separate gate. -/
namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO.FiniteCopy
variable {n t k : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k)
variable (S : ∀ x, GenericIncidence.System (F.original x).simple)

/-- Exactly three sets per local color, independent of the number of owners. -/
def incidenceSets (x : Fin t) :
    Fin (BiInterface.PathWord.pathwidthPalette (2*k+2)*3) → (S x).IncSet :=
  fun j => (S x).parameters (F.guidance x).colors (finProdFinEquiv.symm j)

abbrev IncidenceFamily := Sigma (fun x => (S x).Element)

def mergedIncidenceSets :
    Fin (BiInterface.PathWord.pathwidthPalette (2*k+2)*3) → F.IncidenceFamily S → Prop :=
  OwnerMerge.merge (F.incidenceSets S)

@[simp] theorem mergedIncidenceSets_restrict (x : Fin t)
    (j : Fin (BiInterface.PathWord.pathwidthPalette (2*k+2)*3)) (z : (S x).Element) :
    F.mergedIncidenceSets S j ⟨x,z⟩ ↔ F.incidenceSets S x j z := Iff.rfl

theorem incidence_owners_disjoint {x y : Fin t} (hxy : x≠y)
    (u : (S x).Element) (v : (S y).Element) :
    (⟨x,u⟩ : F.IncidenceFamily S)≠⟨y,v⟩ := by
  intro h
  exact hxy (congrArg Sigma.fst h)

/-- Root/forest incidence validity is produced from each accepted local
pathwidth-guidance output, not added as a family assumption. -/
theorem incidence_colors_valid (x : Fin t)
    (i : Fin (BiInterface.PathWord.pathwidthPalette (2*k+2))) :
    ((S x).colorData ((F.guidance x).colors i)).Valid :=
  (S x).color_valid ((F.guidance x).colors i)

/-- Every actual normalized local bag is captured on its own actual incidence
carrier, retaining the same graph-size-independent palette. -/
theorem normalized_incidence_capture (x : Fin t) (v : Fin (F.vertices x)) :
    ({u | u ∈ (F.normalized x).bag v} : Set (Fin (F.vertices x))).Nonempty →
    ∃ z : (S x).Element, ∀ r ∈ (F.normalized x).bag v, ∃ i,
      (S x).rootRelation ((S x).colorData ((F.guidance x).colors i)).vertices
        ((S x).colorData ((F.guidance x).colors i)).edges
        ((S x).colorData ((F.guidance x).colors i)).roots z (.inl r) :=
  (S x).capture_to_incidence (F.guidance x).colors (F.normalized_capture x v)

#print axioms mergedIncidenceSets_restrict
#print axioms incidence_colors_valid
#print axioms normalized_incidence_capture
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
