import MarginalBagPrerequisites
import MarginalEarlierLocality

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership SameVertexForest ConnectedConeNormalization
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem actualLocalBag_any (x : Fin t) (v : Fin (F.vertices x)) (z : Carrier.Actual (A := A) D) :
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.localBag (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases (Incidence.embed D names x (F.names x) (.inl v)) (fun _ => z))
      (F.actualExtractionSets names hA hG C) ↔
      ∃ u, z=Incidence.embed D names x (F.names x) (.inl u) ∧ u∈(F.normalized x).bag v := by
  classical
  let code := fun u => Incidence.embed D names x (F.names x) (.inl u)
  let X := F.actualExtractionSets names hA hG C
  let colors := BiInterface.PathWord.pathwidthPalette (2*k+2)
  let ats : {r : Nat} → Syntax.OutputAtom r → (Fin r → Carrier.Actual (A := A) D) → Prop := Actual.outputAtoms D names
  have hshape : ActualEval ats (NestedSyntax.localBag colors (0 : Fin 2) 1)
      (Fin.cases (code v) (fun _ => z)) X ↔
      z=code v ∨ ActualEval ats (NestedSyntax.earlier colors (0 : Fin 2) 1)
        (Fin.cases z (fun _ => code v)) X ∧
        ∃ w, ActualEval ats (NestedSyntax.cone colors (0 : Fin 2) 1)
          (Fin.cases (code v) (fun _ => w)) X ∧
          (z≠w ∧ ∃ e, ats .localEdge (fun _ => e) ∧
            ats .incidence (Fin.cases z (fun _ => e)) ∧ ats .incidence (Fin.cases w (fun _ => e))) := by
    simp only [NestedSyntax.localBag,NestedSyntax.disj,ActualEval,not_and_or,not_or,not_not,Fin.cases_zero]
    apply or_congr Iff.rfl
    apply and_congr (NestedSyntax.eval_earlier_values ats 1 0 (Fin.cases (code v) (fun _ => z)) X)
    apply exists_congr
    intro w
    apply and_congr
    · convert (NestedSyntax.eval_cone_values ats colors (0 : Fin 2).succ 0
        (Fin.cases w (Fin.cases (code v) (fun _ => z))) X) using 1; rfl
    · convert (NestedSyntax.eval_marginalAdj_values ats (1 : Fin 2).succ 0
        (Fin.cases w (Fin.cases (code v) (fun _ => z))) X) using 1; rfl
  rw [hshape]
  constructor
  · rintro (hz | ⟨hr,w,hc,ha⟩)
    · exact ⟨v,hz,(F.normalized_mem_iff x v v).mpr (Or.inl rfl)⟩
    · obtain ⟨u,hu,huv⟩ := (F.earlier_into_local names hA hG C x v z).mp hr
      obtain ⟨r,hr,hvr⟩ := (F.actualCone_out names hA hG C x v w).mp hc
      subst z
      subst w
      have hadj := (Incidence.actual_adjacency_iff D names x (F.names x) hA hG C u r).mpr ha
      exact ⟨u,rfl,(F.normalized_mem_iff x v u).mpr (Or.inr ⟨huv,r,hvr,hadj⟩)⟩
  · rintro ⟨u,rfl,hb⟩
    rcases (F.normalized_mem_iff x v u).mp hb with he | ⟨huv,r,hvr,hadj⟩
    · exact Or.inl (congrArg code he)
    · exact Or.inr ⟨(F.actualEarlier_same_owner names hA hG C x u v).mpr huv,code r,
        (F.actualCone_out names hA hG C x v (code r)).mpr ⟨r,rfl,hvr⟩,
        (Incidence.actual_adjacency_iff D names x (F.names x) hA hG C u r).mp hadj⟩

#print axioms actualLocalBag_any
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
