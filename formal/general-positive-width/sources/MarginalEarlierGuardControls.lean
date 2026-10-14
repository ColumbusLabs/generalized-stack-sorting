import MarginalEarlierGuards

namespace StackSorting.GraphWidth.MarginalA2.GuardControls
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy SparseEndpointMSO.IncidenceOwnership
open CapturedLinkExtraction

/-- Three isolated auxiliary edge objects: no vertex and no selected root.
The raw separator preorder is vacuous on this domain. -/
def edgeOnlyAtoms : {r : Nat} → IncidenceAtom r → (Fin r → Fin 3) → Prop
  | _, .edge, _ => True
  | _, _, _ => False

def noSets : Fin (CapturedLinkExtraction.parameterCount 0) → Fin 3 → Prop := fun _ _ => False

theorem raw_auxiliary_earlier (u v : Fin 3) (h : u≠v) :
    ActualEval edgeOnlyAtoms (capturedEarlierFormula (fixedIndices 0) (0 : Fin 2) 1)
      (Fin.cases u (fun _ => v)) noSets := by
  change (∀ r : Fin 3, False → _) ∧ u≠v
  exact ⟨fun _ hf => hf.elim,h⟩

/-- Without endpoint guards, object 1 becomes a spurious middle node between
objects 0 and 2 despite all three being auxiliary edges. -/
theorem raw_spurious_middle :
    ActualEval edgeOnlyAtoms (capturedEarlierFormula (fixedIndices 0) (0 : Fin 2) 1)
      (Fin.cases (0 : Fin 3) (fun _ => 1)) noSets ∧
    ActualEval edgeOnlyAtoms (capturedEarlierFormula (fixedIndices 0) (0 : Fin 2) 1)
      (Fin.cases (1 : Fin 3) (fun _ => 2)) noSets :=
  ⟨raw_auxiliary_earlier 0 1 (by decide),raw_auxiliary_earlier 1 2 (by decide)⟩

def marginalEdgeOnlyAtoms : {r : Nat} → Syntax.OutputAtom r → (Fin r → Fin 3) → Prop
  | _, .localEdge, _ => True
  | _, _, _ => False

/-- Positive rejection control for the corrected full-domain formula. -/
theorem guarded_no_auxiliary_earlier (u v : Fin 3) :
    ¬ ActualEval marginalEdgeOnlyAtoms (NestedSyntax.earlier 0 (0 : Fin 2) 1)
      (Fin.cases u (fun _ => v)) noSets := by
  intro h
  exact h.1.elim

/-- Distinct original vertices assigned to distinct owners cannot form an
existential middle-node link, even when the unrelativized preorder is vacuous. -/
def separatedOwnerAtoms : {r : Nat} → Syntax.OutputAtom r → (Fin r → Fin 3) → Prop
  | _, .vertex, _ => True
  | _, .owner, env => env 0=env 1
  | _, _, _ => False

theorem guarded_no_wrong_owner (u v : Fin 3) (hne : u≠v) :
    ¬ ActualEval separatedOwnerAtoms (NestedSyntax.earlier 0 (0 : Fin 2) 1)
      (Fin.cases u (fun _ => v)) noSets := by
  intro h
  obtain ⟨owner,hu,hv⟩ := NestedSyntax.earlier_owner separatedOwnerAtoms 0 1 _ noSets h
  change u=owner at hu
  change v=owner at hv
  exact hne (hu.trans hv.symm)

#print axioms guarded_no_wrong_owner
#print axioms raw_spurious_middle
#print axioms guarded_no_auxiliary_earlier
end StackSorting.GraphWidth.MarginalA2.GuardControls
