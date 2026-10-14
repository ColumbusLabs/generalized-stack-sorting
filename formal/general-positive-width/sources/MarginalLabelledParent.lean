import MarginalLabelledCodes

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem forestParent_labels (x y : Fin t) (u : Fin (F.vertices x)) (v : Fin (F.vertices y)) :
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.forestParent (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases (Incidence.embed D names x (F.names x) (.inl u))
        (fun _ => Incidence.embed D names y (F.names y) (.inl v)))
      (F.actualExtractionSets names hA hG C) ↔
      (⟨y,some v⟩ : F.LocalLabels)=⟨x,RootedLocal.parent (F.normalized x).order (some u)⟩ := by
  classical
  rw [F.actualForestParent_any names hA hG C]
  constructor
  · rintro ⟨w,he,hw⟩
    have hn : w≠u := fun h => (F.normalized x).order.irrefl u (h ▸ hw.1)
    have hp := ((F.normalized x).order.parent_eq_iff_cover hn).mpr hw
    have hl := (F.local_vertex_code_eq names y x v w).mp he
    simpa only [RootedLocal.parent,hp,ite_eq_right hn] using hl
  · intro hl
    by_cases hp : (F.normalized x).order.parent u=u
    · have he := congrArg F.localLabelsEquiv hl
      simp [RootedLocal.parent,hp,localLabelsEquiv,flattenLocal] at he
    · have hl' : (⟨y,some v⟩ : F.LocalLabels)=⟨x,some ((F.normalized x).order.parent u)⟩ := by
        simpa only [RootedLocal.parent,ite_eq_right hp] using hl
      exact ⟨_,(F.local_vertex_code_eq names y x v _).mpr hl',
        (F.normalized x).order.parent_cover ((F.normalized x).order.parent_rel hp)⟩

theorem forestRoot_parent_labels (x y : Fin t) (u : Fin (F.vertices x)) :
    (ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.forestRoot (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 1))
      (fun _ => Incidence.embed D names x (F.names x) (.inl u))
      (F.actualExtractionSets names hA hG C) ∧
      Actual.outputAtoms D names .owner
        (Fin.cases (Incidence.embed D names x (F.names x) (.inl u)) (fun _ => .inl (Actual.node y)))) ↔
      (⟨y,none⟩ : F.LocalLabels)=⟨x,RootedLocal.parent (F.normalized x).order (some u)⟩ := by
  classical
  rw [F.actualForestRoot names hA hG C,F.local_owner_vertex names]
  constructor
  · rintro ⟨hp,rfl⟩
    simp only [RootedLocal.parent,hp,ite_true]
  · intro hl
    have hy := congrArg Sigma.fst hl
    have hp : (F.normalized x).order.parent u=u := by
      by_contra hp
      have he := congrArg F.localLabelsEquiv hl
      simp [RootedLocal.parent,hp,localLabelsEquiv,flattenLocal] at he
    exact ⟨hp,hy.symm⟩

#print axioms forestParent_labels
#print axioms forestRoot_parent_labels
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
