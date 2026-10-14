import MarginalLabelledCarrier
import MarginalParentLocality
import MarginalLocalBagSemantics

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (X : Fin (CapturedLinkExtraction.parameterCount (BiInterface.PathWord.pathwidthPalette (2*k+2))) →
  Carrier.Actual (A := A) D → Prop)

noncomputable def labelledCodeEquiv : F.LabelledCarrier ≃ NestedCodes.Step D names X :=
  F.labelledFlatEquiv.trans (NestedCodes.codeEquiv D names X)

@[simp] theorem labelled_code_original (v : Fin n) :
    (F.labelledCodeEquiv names X (.inl v)).val=(0,.inl (Actual.vertex names v)) := rfl
@[simp] theorem labelled_code_outer (x : Fin t) :
    (F.labelledCodeEquiv names X (.inr (.inl x))).val=(0,.inl (Actual.node x)) := rfl
@[simp] theorem labelled_code_some (x : Fin t) (u : Fin (F.vertices x)) :
    (F.labelledCodeEquiv names X (.inr (.inr ⟨x,some u⟩))).val=
      (1,Incidence.embed D names x (F.names x) (.inl u)) := rfl
@[simp] theorem labelled_code_none (x : Fin t) :
    (F.labelledCodeEquiv names X (.inr (.inr ⟨x,none⟩))).val=(2,.inl (Actual.node x)) := rfl

theorem local_vertex_code_eq (x y : Fin t) (u : Fin (F.vertices x)) (v : Fin (F.vertices y)) :
    Incidence.embed D names x (F.names x) (.inl u)=Incidence.embed D names y (F.names y) (.inl v) ↔
      (⟨x,some u⟩ : F.LocalLabels)=⟨y,some v⟩ := by
  constructor
  · intro h
    apply F.localLabelsEquiv.injective
    apply congrArg Sum.inl
    exact (Actual.vertex_inj names).mp (Sum.inl.inj h)
  · intro h
    have he := congrArg F.localLabelsEquiv h
    exact congrArg (fun v => (Sum.inl (Actual.vertex names v) : Carrier.Actual (A := A) D)) (Sum.inl.inj he)

theorem local_owner_vertex (x y : Fin t) (u : Fin (F.vertices x)) :
    Actual.outputAtoms D names .owner
      (Fin.cases (Incidence.embed D names x (F.names x) (.inl u)) (fun _ => .inl (Actual.node y))) ↔ x=y := by
  simpa only [Incidence.embed,Actual.vertex,Equiv.symm_apply_apply,(F.names x u).property] using
    (Incidence.owner_vertex_exact D names y (names (F.names x u).val))

theorem root_label_eq (x y : Fin t) : (⟨x,none⟩ : F.LocalLabels)=⟨y,none⟩ ↔ x=y := by
  constructor
  · exact congrArg Sigma.fst
  · intro h; subst y; rfl

variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem actualLocalBag_global (x : Fin t) (v : Fin (F.vertices x)) (w : Fin n) :
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.localBag (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases (Incidence.embed D names x (F.names x) (.inl v)) (fun _ => .inl (Actual.vertex names w)))
      (F.actualExtractionSets names hA hG C) ↔
      ∃ u, u∈(F.normalized x).bag v ∧ (F.names x u).val=w := by
  rw [F.actualLocalBag_any names hA hG C]
  constructor
  · rintro ⟨u,hu,hb⟩
    exact ⟨u,hb,((Actual.vertex_inj names).mp (Sum.inl.inj hu)).symm⟩
  · rintro ⟨u,hb,hu⟩
    exact ⟨u,congrArg (fun w => (Sum.inl (Actual.vertex names w) : Carrier.Actual (A := A) D)) hu.symm,hb⟩

#print axioms labelledCodeEquiv
#print axioms local_vertex_code_eq
#print axioms actualLocalBag_global
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
