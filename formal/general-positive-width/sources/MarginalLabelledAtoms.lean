import MarginalLabelledOwner
import MarginalLabelledMargin
import MarginalLabelledAdhesion
import MarginalLabelledOuterParent
import MarginalLabelledOriginalEdge
import MarginalLabelledLocalParent
import MarginalLabelledLocalBag

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.FiniteCopy.Parametric CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem labelled_binary (a : Nested.Syntax.InputAtom 2) (u v : F.LabelledCarrier) :
    F.labelledEval2 names hA hG C a u v ↔ Nested.Syntax.atoms F.labelledRelations a (Fin.cases u (fun _ => v)) := by
  cases a with
  | owner => exact F.labelled_owner names hA hG C u v
  | margin => exact F.labelled_margin names hA hG C u v
  | adhesion => exact F.labelled_adhesion names hA hG C u v
  | outerParent => exact F.labelled_outerParent names hA hG C u v
  | localParent => exact F.labelled_localParent names hA hG C u v
  | localBag => exact F.labelled_localBag names hA hG C u v
  | originalEdge => exact F.labelled_originalEdge names hA hG C u v

theorem labelled_atoms_one (a : Nested.Syntax.InputAtom 1) (env : Fin 1 → F.LabelledCarrier) :
    stepAtoms (NestedSyntax.interpretation (BiInterface.PathWord.pathwidthPalette (2*k+2)))
      (Actual.outputAtoms D names) (F.actualExtractionSets names hA hG C) a
      (fun i => F.localCode names hA hG C (env i)) ↔ Nested.Syntax.atoms F.labelledRelations a env := by
  have he : env=(fun _ => env 0) := by funext i; fin_cases i; rfl
  rw [he]
  exact F.labelled_unary names hA hG C a (env 0)

theorem labelled_atoms_two (a : Nested.Syntax.InputAtom 2) (env : Fin 2 → F.LabelledCarrier) :
    stepAtoms (NestedSyntax.interpretation (BiInterface.PathWord.pathwidthPalette (2*k+2)))
      (Actual.outputAtoms D names) (F.actualExtractionSets names hA hG C) a
      (fun i => F.localCode names hA hG C (env i)) ↔ Nested.Syntax.atoms F.labelledRelations a env := by
  have he : env=Fin.cases (env 0) (fun _ => env 1) := by funext i; fin_cases i <;> rfl
  have hc : (fun i => F.localCode names hA hG C (env i))=
      Fin.cases (F.localCode names hA hG C (env 0)) (fun _ => F.localCode names hA hG C (env 1)) := by
    funext i; fin_cases i <;> rfl
  rw [hc]
  have h := F.labelled_binary names hA hG C a (env 0) (env 1)
  rw [←he] at h
  exact h

theorem labelled_atoms {r : Nat} (a : Nested.Syntax.InputAtom r) (env : Fin r → F.LabelledCarrier) :
    stepAtoms (NestedSyntax.interpretation (BiInterface.PathWord.pathwidthPalette (2*k+2)))
      (Actual.outputAtoms D names) (F.actualExtractionSets names hA hG C) a
      (fun i => F.localCode names hA hG C (env i)) ↔ Nested.Syntax.atoms F.labelledRelations a env := by
  cases a with
  | original => exact F.labelled_atoms_one names hA hG C .original env
  | localNode => exact F.labelled_atoms_one names hA hG C .localNode env
  | localRoot => exact F.labelled_atoms_one names hA hG C .localRoot env
  | owner => exact F.labelled_atoms_two names hA hG C .owner env
  | margin => exact F.labelled_atoms_two names hA hG C .margin env
  | adhesion => exact F.labelled_atoms_two names hA hG C .adhesion env
  | outerParent => exact F.labelled_atoms_two names hA hG C .outerParent env
  | localParent => exact F.labelled_atoms_two names hA hG C .localParent env
  | localBag => exact F.labelled_atoms_two names hA hG C .localBag env
  | originalEdge => exact F.labelled_atoms_two names hA hG C .originalEdge env

#print axioms labelled_atoms
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
