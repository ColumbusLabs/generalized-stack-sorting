import MarginalNestedPhysicalCode

namespace StackSorting.GraphWidth.MarginalA2
open FinitePort Nested SparseEndpointMSO SparseEndpointMSO.FiniteCopy SparseEndpointMSO.FiniteCopy.Parametric
open SparseEndpointMSO.IncidenceOwnership CapturedLinkExtraction

noncomputable abbrev localColors (k : Nat) := BiInterface.PathWord.pathwidthPalette (2*k+2)
abbrev presentationCopies (c W : Nat) := 3*(Syntax.copies W*c)
noncomputable abbrev presentationParameters (c d k W : Nat) :=
  (d+Syntax.parameters W*c)+CapturedLinkExtraction.parameterCount (localColors k)*(Syntax.copies W*c)

noncomputable def presentation {c d : Nat} (J : Parametric.Interpretation Syntax.InputAtom c d) (k W : Nat) :
    Parametric.Interpretation Nested.Syntax.InputAtom (presentationCopies c W) (presentationParameters c d k W) :=
  Parametric.compose (Parametric.compose J (Syntax.interpretation W)) (NestedSyntax.interpretation (localColors k))

theorem presentation_copy_count (c W : Nat) : presentationCopies c W=3*((1+W*W)*c) := by
  rw [presentationCopies,Syntax.copy_count]

theorem presentation_parameter_count (c d k W : Nat) :
    presentationParameters c d k W=(d+(W+W*W)*c)+CapturedLinkExtraction.parameterCount (localColors k)*((1+W*W)*c) := by
  rw [presentationParameters,Syntax.parameter_count,Syntax.copy_count]

namespace Local.PathFamily
variable {A : Model} {n t k W c d : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (ht : 0<t) (hm : ∀ x, ∃ v, introductionNode D v=x)
variable (hc : ConnectedIntroductionComponents D)
variable (names : Fin n ≃ IncidenceOwnership.Vertex A) (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)
variable {J : Parametric.Interpretation Syntax.InputAtom c d} {params : Fin d → Nat → Prop}
variable (R : Parametric.Realization J A params (Carrier.Base A t) (Actual.outerAtoms D names))

noncomputable def presentationSets : Fin (presentationParameters c d k W) → Nat → Prop :=
  let RM := Actual.realization D names C R
  Parametric.flattenedSets
    (Parametric.flattenedSets params (fun i => R.liftSet (Carrier.sets D names C i)))
    (fun i => RM.liftSet (F.actualExtractionSets names hA hG C i))

/-- Complete actual A.2 presentation from C.2 and the independently supplied
actual 5.9 path family. Local guidance, normalized rooted bags, node codes,
edge deduplication and disjoint parameter merging are all constructed. -/
noncomputable def presentationRealization :
    Parametric.Realization (presentation J k W) A (F.presentationSets names hA hG C R)
      (CarrierSemantics.Carrier (F.rootedNestedInput ht hm hc))
      (Nested.Syntax.atoms (CarrierSemantics.relations (F.rootedNestedInput ht hm hc))) :=
  F.nestedRealization ht hm hc names hA hG C (Actual.realization D names C R)

theorem presentation_supported (hp : CanonicalChoice.SupportedTuple A params) :
    CanonicalChoice.SupportedTuple A (F.presentationSets names hA hG C R) :=
  (Actual.realization D names C R).flattened_actual_supported
    (R.flattened_actual_supported hp (Carrier.sets D names C))
    (F.actualExtractionSets names hA hG C)

theorem presentation_original_rep (tag : Fin c) (number : Nat) (v : Fin n) :
    (F.presentationRealization ht hm hc names hA hG C R).rep (fullRetainedTag W tag,number) (.inl v) ↔
      R.rep (tag,number) (Actual.vertex names v) :=
  (F.nested_original_rep ht hm hc names hA hG C (Actual.realization D names C R)
    (finProdFinEquiv (marginalRetainedTag W,tag)) number v).trans
    (marginal_original_rep D names C R tag number v)

theorem presentation_local_bound (x : Fin t) :
    ((F.rootedNestedInput ht hm hc).localDecomp x).BagBound (localColors k) :=
  F.rootedNestedInput_bound ht hm hc x

#print axioms presentationRealization
#print axioms presentation_supported
#print axioms presentation_original_rep
end Local.PathFamily
end StackSorting.GraphWidth.MarginalA2
