import MarginalNestedCodes
import NestedCarrierSemantics

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
variable {A : Model} {n t k : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (ht : 0<t) (hm : ∀ x, ∃ v, introductionNode D v=x)
variable (hc : ConnectedIntroductionComponents D)

/-- The actual numbered local nodes are transported to the exact q+1 labels;
this equivalence preserves the entire original and outer carriers literally. -/
noncomputable def nestedFlatEquiv :
    CarrierSemantics.Carrier (F.rootedNestedInput ht hm hc) ≃ NestedCodes.FlatCarrier n t :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sigmaCongrRight F.rootedNames).trans F.localLabelsEquiv))

@[simp] theorem nestedFlat_original (v : Fin n) :
    F.nestedFlatEquiv ht hm hc (.inl v)=.inl v := rfl
@[simp] theorem nestedFlat_outer (x : Fin t) :
    F.nestedFlatEquiv ht hm hc (.inr (.inl x))=.inr (.inl x) := rfl
@[simp] theorem nestedFlat_local (x : Fin t)
    (j : Fin (Fintype.card (RootedLocal.Node (F.vertices x)))) :
    F.nestedFlatEquiv ht hm hc (.inr (.inr ⟨x,j⟩))=
      .inr (.inr (F.localLabelsEquiv ⟨x,F.rootedNames x j⟩)) := rfl

variable (names : Fin n ≃ SparseEndpointMSO.IncidenceOwnership.Vertex A)
variable (X : Fin (CapturedLinkExtraction.parameterCount (BiInterface.PathWord.pathwidthPalette (2*k+2))) →
  Carrier.Actual (A := A) D → Prop)

/-- Genuine finite-copy code bijection for the actual nested carrier. -/
noncomputable def nestedCodeEquiv :
    CarrierSemantics.Carrier (F.rootedNestedInput ht hm hc) ≃ NestedCodes.Step D names X :=
  (F.nestedFlatEquiv ht hm hc).trans (NestedCodes.codeEquiv D names X)

@[simp] theorem nested_original_code (v : Fin n) :
    (F.nestedCodeEquiv ht hm hc names X (.inl v)).val=(0,.inl (Actual.vertex names v)) := rfl

#print axioms nestedCodeEquiv
#print axioms nested_original_code
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
