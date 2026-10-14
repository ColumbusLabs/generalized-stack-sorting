import MarginalLabelledParent
import MarginalOriginalAdjacency

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

noncomputable abbrev localCode := F.labelledCodeEquiv names (F.actualExtractionSets names hA hG C)

noncomputable def labelledEval1 (a : Nested.Syntax.InputAtom 1) (z : F.LabelledCarrier) : Prop :=
  stepAtoms (NestedSyntax.interpretation (BiInterface.PathWord.pathwidthPalette (2*k+2)))
    (Actual.outputAtoms D names) (F.actualExtractionSets names hA hG C) a (fun _ => F.localCode names hA hG C z)

noncomputable def labelledEval2 (a : Nested.Syntax.InputAtom 2) (u v : F.LabelledCarrier) : Prop :=
  stepAtoms (NestedSyntax.interpretation (BiInterface.PathWord.pathwidthPalette (2*k+2)))
    (Actual.outputAtoms D names) (F.actualExtractionSets names hA hG C) a
    (Fin.cases (F.localCode names hA hG C u) (fun _ => F.localCode names hA hG C v))

theorem labelledEval2_formula (a : Nested.Syntax.InputAtom 2) (u v : F.LabelledCarrier) :
    F.labelledEval2 names hA hG C a u v ↔
      ActualEval (Actual.outputAtoms D names)
        (NestedSyntax.atom (BiInterface.PathWord.pathwidthPalette (2*k+2)) a
          (Fin.cases (F.localCode names hA hG C u).val.1 (fun _ => (F.localCode names hA hG C v).val.1)))
        (Fin.cases (F.localCode names hA hG C u).val.2 (fun _ => (F.localCode names hA hG C v).val.2))
        (F.actualExtractionSets names hA hG C) := by
  unfold labelledEval2 stepAtoms
  have htag : (fun i : Fin 2 => (Fin.cases (motive := fun _ : Fin 2 => NestedCodes.Step D names (F.actualExtractionSets names hA hG C)) (F.localCode names hA hG C u)
      (fun _ => F.localCode names hA hG C v) i).val.1)=
      Fin.cases (F.localCode names hA hG C u).val.1 (fun _ => (F.localCode names hA hG C v).val.1) := by
    funext i; fin_cases i <;> rfl
  have hbase : (fun i : Fin 2 => (Fin.cases (motive := fun _ : Fin 2 => NestedCodes.Step D names (F.actualExtractionSets names hA hG C)) (F.localCode names hA hG C u)
      (fun _ => F.localCode names hA hG C v) i).val.2)=
      Fin.cases (F.localCode names hA hG C u).val.2 (fun _ => (F.localCode names hA hG C v).val.2) := by
    funext i; fin_cases i <;> rfl
  rw [htag,hbase]
  rfl

#print axioms labelledEval2_formula
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
