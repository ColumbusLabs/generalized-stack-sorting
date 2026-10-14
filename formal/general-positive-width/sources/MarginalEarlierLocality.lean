import MarginalEarlierSemantics
import MarginalEarlierGuards

namespace StackSorting.GraphWidth.MarginalA2.Local.PathFamily
open FinitePort Nested GuidedPathwidth SparseEndpointMSO SparseEndpointMSO.FiniteCopy
open CapturedLinkExtraction SparseEndpointMSO.IncidenceOwnership
variable {A : Model} {n t k W : Nat} {G : Graph n} {T : RootedTree t} {D : Decomposition G T}
variable (F : PathFamily D k) (names : Fin n ≃ IncidenceOwnership.Vertex A)
variable (hA : Laws A)
variable (hG : ∀ u v, G.Adj u v ↔ Adjacent A (names u).val (names v).val)
variable (C : AdhesionColoring D W)

/-- Every full-domain predecessor of a local vertex is another original
vertex in that same actual margin. In particular no auxiliary edge, outer
node, or other owner's vertex can serve as an existential intermediate node. -/
theorem earlier_into_local (x : Fin t) (u : Fin (F.vertices x)) (z : Carrier.Actual (A := A) D) :
    ActualEval (Actual.outputAtoms D names)
      (NestedSyntax.earlier (BiInterface.PathWord.pathwidthPalette (2*k+2)) (0 : Fin 2) 1)
      (Fin.cases z (fun _ => Incidence.embed D names x (F.names x) (.inl u)))
      (F.actualExtractionSets names hA hG C) ↔
      ∃ v : Fin (F.vertices x), z=Incidence.embed D names x (F.names x) (.inl v) ∧
        (F.normalized x).order.rel v u := by
  constructor
  · intro h
    have hz := (NestedSyntax.earlier_vertices (Actual.outputAtoms D names) 0 1 _ _ h).1
    obtain ⟨owner,hzo,huo⟩ := NestedSyntax.earlier_owner (Actual.outputAtoms D names) 0 1 _ _ h
    have ho := Actual.owner_functional D names huo
      (Incidence.embed_owned D names x (F.names x) (.inl u))
    subst owner
    obtain ⟨a,ha⟩ := Incidence.owner_covered D names x (F.names x) z hzo
    subst z
    obtain ⟨v,hv⟩ := (Incidence.embed_vertex D names x (F.names x) a).mp hz
    subst a
    exact ⟨v,rfl,(F.actualEarlier_same_owner names hA hG C x v u).mp h⟩
  · rintro ⟨v,rfl,h⟩
    exact (F.actualEarlier_same_owner names hA hG C x v u).mpr h

#print axioms earlier_into_local
end StackSorting.GraphWidth.MarginalA2.Local.PathFamily
