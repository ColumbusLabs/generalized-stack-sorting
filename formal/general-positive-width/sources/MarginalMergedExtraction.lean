import MarginalIncidenceAtoms
import MarginalLocalExtraction
import OwnerParameterUnion

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

/-- The local incidence family is constructed from actual marginal edges. -/
noncomputable def actualSystems (x : Fin t) : GenericIncidence.System (F.original x).simple :=
  Incidence.system D names x (F.names x) hA hG C

def familyEmbed : (Sigma fun x => Fin (F.vertices x) ⊕ Incidence.Edge D names x) → Carrier.Actual (A := A) D :=
  fun z => Incidence.embed D names z.1 (F.names z.1) z.2

 theorem familyEmbed_injective : Function.Injective (F.familyEmbed names) := by
  apply OwnerMerge.family_injective (fun x => Incidence.embed D names x (F.names x))
    (fun z x => Actual.outputAtoms D names .owner (Fin.cases z (fun _ => .inl (Actual.node x))))
  · exact fun x z => Incidence.embed_owned D names x (F.names x) z
  · intro z x y hx hy
    exact (Actual.node_inj).mp (Sum.inl.inj (Actual.owner_functional D names hx hy))
  · exact fun x => Incidence.embed_injective D names x (F.names x)

/-- One fixed tuple over the whole marginal carrier. The owner count never
appears in its arity, and ancillary outer nodes/crossing edges receive no sets. -/
noncomputable def actualExtractionSets :
    Fin (CapturedLinkExtraction.parameterCount (BiInterface.PathWord.pathwidthPalette (2*k+2))) → Carrier.Actual (A := A) D → Prop :=
  OwnerMerge.union (F.familyEmbed names) (F.extractionSets (F.actualSystems names hA hG C))

 theorem actualExtractionSets_restrict (x : Fin t)
    (j : Fin (CapturedLinkExtraction.parameterCount (BiInterface.PathWord.pathwidthPalette (2*k+2))))
    (z : Fin (F.vertices x) ⊕ Incidence.Edge D names x) :
    F.actualExtractionSets names hA hG C j (Incidence.embed D names x (F.names x) z) ↔
      F.extractionSets (F.actualSystems names hA hG C) x j z :=
  OwnerMerge.union_restrict (F.familyEmbed names) (F.familyEmbed_injective names)
    (F.extractionSets (F.actualSystems names hA hG C)) x j z

#print axioms familyEmbed_injective
#print axioms actualExtractionSets_restrict
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
