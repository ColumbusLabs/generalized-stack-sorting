import SaneSuppliedPartsEndpoint
import RoutedAdhesionIncidence
import OuterPhysicalVertexCode
import InheritedMarginalColoring

namespace StackSorting.GraphWidth.GeneralConstruction
open FinitePort Nested
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership CapturedLinkExtraction
open GuidedPathwidth

abbrev outerPalette (k : Nat) := 4*k^3+2*k
abbrev outerCopies (k : Nat) := 2*(CapturedLinkExtraction.MultiMargin.CompletionIncidence.count (outerPalette k)*3)
abbrev outerParameters (k : Nat) :=
  (0+CapturedLinkExtraction.parameterCount (outerPalette k)*3)+
    4*(CapturedLinkExtraction.MultiMargin.CompletionIncidence.count (outerPalette k)*3)

/-- A fixed interpretation depending only on the supplied width parameter. -/
noncomputable def outerInterpretation (k : Nat) := MultiMargin.ActualC2.interpretation (outerPalette k)

variable {A : Model} {n s : Nat} {G : Graph n} {S : RootedTree s}

/-- Every field refers to the same actual constructed outer decomposition.
All graph-size dependence is data; the interpretation and parameter arity
are fixed solely by k. Original vertex names and edge identities are retained. -/
structure OuterPresentation (original : Decomposition G S) (k : Nat)
    (names : Fin n ≃ Vertex A) (hA : Laws A)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val) where
  size : Nat
  tree : RootedTree size
  outer : Decomposition G tree
  nonempty : 0<size
  sane : MultiMargin.Sane outer
  marginalPaths : MarginalA2.Local.PathFamily outer k
  adhesionColoring : MarginalA2.AdhesionColoring outer (k+1)
  containment : ∀ i, ∃ x, ∀ v, outerAdhesion outer i v → v∈original.bag x
  params : Fin (outerParameters k) → Nat → Prop
  supported : CanonicalChoice.SupportedTuple A params
  realization : Parametric.Realization (outerInterpretation k) A params
    (IncidenceOwnership.Element A ⊕ Fin size) (MultiMargin.ActualC2.retained outer names hA hG).outputAtoms
  vertexCode : ∀ v, realization.rep (MultiMargin.ActualC2.physicalVertexTag (outerPalette k),(names v).val)
    (.inl (.inl (names v)))

/-- Width, actual connectedness and the genuine original incidence model
construct all outer data needed by A.2. No outer guidance or representation
witness is supplied. -/
theorem exists_outer_presentation (D : Decomposition G S) (k : Nat)
    (connected : ∀ u v, Walk G.Adj (fun _ => True) u v)
    (hn : 0<n) (width : D.BagBound (k+1))
    (names : Fin n ≃ Vertex A) (hA : Laws A)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val) :
    Nonempty (OuterPresentation D k names hA hG) := by
  obtain ⟨m,T,E,ht,hs,⟨P,hP⟩,⟨F⟩,hcontain⟩ :=
    LowPathwidthParts.exists_sane_supplied_low_pathwidth_parts D connected hn k width
  have hcontain' : ∀ i, ∃ x, ∀ v, outerAdhesion E i v → v∈D.bag x := by
    intro i
    obtain ⟨x,hx⟩ := hcontain i
    exact ⟨x,fun v hv => hx v ((MultiMargin.adhesion_iff E i v).mpr hv)⟩
  obtain ⟨K⟩ := MarginalA2.exists_adhesionColoring D E width hcontain'
  obtain ⟨C,hC,hcap⟩ := routed_adhesions_incidence E P hP hA names hG
  obtain ⟨params,hparams,R,hcode⟩ :=
    MultiMargin.ActualC2.exists_supported_physical_realization E names C hC hcap hA hG hs ht
  exact ⟨⟨m,T,E,ht,hs,F,K,hcontain',params,hparams,R,hcode⟩⟩

#print axioms exists_outer_presentation
end StackSorting.GraphWidth.GeneralConstruction
