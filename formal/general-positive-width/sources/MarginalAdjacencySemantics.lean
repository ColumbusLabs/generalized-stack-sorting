import MarginalIncidentOwner
import GenericIncidenceAdjacency

namespace StackSorting.GraphWidth.MarginalA2.Incidence
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership SparseEndpointMSO.FiniteCopy
open FinitePort Nested Actual GuidedPathwidth
variable {A : Model} {n t q W : Nat} {G : Graph n} {T : RootedTree t}
variable (D : Decomposition G T) (names : Fin n ≃ Vertex A)
variable (x : Fin t) (localNames : Fin q ≃ {v : Fin n // introductionNode D v=x})
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

include hA hG C in
theorem actual_adjacency_iff (u v : Fin q) : (marginalGraph D x localNames).Adj u v ↔
    embed D names x localNames (.inl u)≠embed D names x localNames (.inl v) ∧
    ∃ e : Carrier.Actual (A := A) D, outputAtoms D names .localEdge (fun _ => e) ∧
      outputAtoms D names .incidence (Fin.cases (embed D names x localNames (.inl u)) (fun _ => e)) ∧
      outputAtoms D names .incidence (Fin.cases (embed D names x localNames (.inl v)) (fun _ => e)) := by
  let S := system D names x localNames hA hG C
  change (Local.graphOriginal (marginalGraph D x localNames)).simple.Adj u v ↔ _
  rw [S.adjacency_iff]
  constructor
  · rintro ⟨hne,e,he,hu,hv⟩
    cases e with
    | inl e => exact he.elim
    | inr e =>
      refine ⟨fun h => hne (Sum.inl.inj (embed_injective D names x localNames h)),
        embed D names x localNames (.inr e),(embed_edge D names x localNames _).mpr ⟨e,rfl⟩,?_,?_⟩
      · exact (embed_incident D names x localNames (.inl u) (.inr e)).mpr hu
      · exact (embed_incident D names x localNames (.inl v) (.inr e)).mpr hv
  · rintro ⟨hne,e,he,hu,hv⟩
    obtain ⟨a,ha⟩ := owner_covered D names x localNames e (incident_owned D names x localNames u e hu)
    subst e
    obtain ⟨edge,hedge⟩ := (embed_edge D names x localNames a).mp he
    subst a
    exact ⟨fun h => hne (congrArg (fun u => embed D names x localNames (.inl u)) h),
      .inr edge,trivial,(embed_incident D names x localNames (.inl u) (.inr edge)).mp hu,
      (embed_incident D names x localNames (.inl v) (.inr edge)).mp hv⟩

#print axioms actual_adjacency_iff
end StackSorting.GraphWidth.MarginalA2.Incidence
