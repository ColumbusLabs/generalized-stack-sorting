import MarginalAdjacencySemantics
import MarginalEarlierSuccessors
import MarginalEarlierValues

namespace StackSorting.GraphWidth.MarginalA2.NestedSyntax
open SparseEndpointMSO SparseEndpointMSO.FiniteCopy
variable {α : Type} {a b : Nat}

theorem eval_marginalAdj_values (ats : {r : Nat} → InputAtom r → (Fin r → α) → Prop)
    (u v : Fin a) (env : Fin a → α) (sets : Fin b → α → Prop) :
    ActualEval ats (marginalAdj u v) env sets ↔ env u≠env v ∧ ∃ e,
      ats .localEdge (fun _ => e) ∧ ats .incidence (Fin.cases (env u) (fun _ => e)) ∧
        ats .incidence (Fin.cases (env v) (fun _ => e)) := by
  simp only [marginalAdj,ActualEval,eval_binary_values,unary,Fin.cases_zero,Fin.cases_succ]

theorem eval_cone_values (ats : {r : Nat} → InputAtom r → (Fin r → α) → Prop)
    (colors : Nat) (u v : Fin a) (env : Fin a → α)
    (sets : Fin (CapturedLinkExtraction.parameterCount colors) → α → Prop) :
    ActualEval ats (cone colors u v) env sets ↔
      ActualEval ats (cone colors (0 : Fin 2) 1) (Fin.cases (env u) (fun _ => env v)) sets := by
  classical
  simp only [cone,disj,ActualEval,not_and_or,not_not,Fin.cases_zero]
  exact or_congr Iff.rfl (eval_earlier_values ats u v env sets)

end StackSorting.GraphWidth.MarginalA2.NestedSyntax

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership SameVertexForest ConnectedConeNormalization
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

theorem actualCone_out (x : Fin t) (u : Fin (F.vertices x)) (z : Carrier.Actual (A := A) D) :
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.cone (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases (Incidence.embed D names x (F.names x) (.inl u)) (fun _ => z))
      (F.actualExtractionSets names hA hG C) ↔
      ∃ v, z=Incidence.embed D names x (F.names x) (.inl v) ∧ Cone (F.normalized x).order u v := by
  classical
  simp only [NestedSyntax.cone,NestedSyntax.disj,ActualEval,not_and_or,not_not,Fin.cases_zero]
  constructor
  · rintro (h | h)
    · exact ⟨u,h.symm,Or.inr rfl⟩
    · obtain ⟨v,hv,hr⟩ := (F.earlier_out_of_local names hA hG C x u z).mp h
      exact ⟨v,hv,Or.inl hr⟩
  · rintro ⟨v,rfl,h | h⟩
    · exact Or.inr ((F.actualEarlier_same_owner names hA hG C x u v).mpr h)
    · exact Or.inl (congrArg (fun u => Incidence.embed D names x (F.names x) (.inl u)) h)

theorem normalized_mem_iff (x : Fin t) (v u : Fin (F.vertices x)) :
    u∈(F.normalized x).bag v ↔ RegionBag (F.graph x) (F.normalized x).order v u := by
  change u∈eliminationFrontierSet (F.normalized x).order.forest (F.graph x) v ↔ _
  simp only [eliminationFrontierSet,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (regionBag_iff_frontier (F.graph x) (F.normalized x).order v u).symm

#print axioms actualCone_out
#print axioms normalized_mem_iff
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
