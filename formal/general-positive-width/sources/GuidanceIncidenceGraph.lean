import GuidanceIncidenceSets
import ForestDisjointUnion

namespace StackSorting.GuidedPathwidth.IncidenceAdapter
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership
variable {D : Model} {n : Nat} {G : SimpleGraph (Fin n)} {P : Set (Fin n)}

/-- The actual selected incidence edges give precisely the forest adjacency
on named original vertices, including successor/matching overlap ownership. -/
theorem selected_step_iff (hD : Laws D) (names : Fin n ≃ Vertex D)
    (hG : ∀ x y, G.Adj x y ↔ Adjacent D (names x).val (names y).val)
    (C : RootedColor G P) (x y : Fin n) :
    Guidance.Step (colorData names C).vertices (colorData names C).edges
      (namedVertex names x) (namedVertex names y) ↔ C.graph.Adj x y := by
  constructor
  · rintro ⟨_,_,_,_,hne,e,he,hF,hi,hj⟩
    cases e with
    | inl v => exact he.elim
    | inr e =>
      have hx := (incident_named_iff names x e).mp hi
      have hy := (incident_named_iff names y e).mp hj
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact False.elim (hne rfl)
      · exact hF
      · exact C.graph.adj_symm hF
      · exact False.elim (hne rfl)
  · intro hxy
    obtain ⟨e,he⟩ := (edge_coverage hD (names x).val (names y).val).mp
      ((hG x y).mp (C.subgraph hxy))
    have hn : namedVertex names x ≠ namedVertex names y := by
      intro h
      exact hxy.ne (names.injective (Sum.inl.inj h))
    refine ⟨trivial,?_,trivial,?_,hn,.inr e,trivial,?_,?_,?_⟩
    · exact (color_vertices_named names C x).mpr (C.edgeSelected hxy).1
    · exact (color_vertices_named names C y).mpr (C.edgeSelected hxy).2
    · rcases he with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · have ha : leftName names e = x := by
          apply names.injective
          apply Subtype.ext
          simpa using hl
        have hb : rightName names e = y := by
          apply names.injective
          apply Subtype.ext
          simpa using hr
        change C.graph.Adj (leftName names e) (rightName names e)
        rw [ha,hb]
        exact hxy
      · have ha : leftName names e = y := by
          apply names.injective
          apply Subtype.ext
          simpa using hl
        have hb : rightName names e = x := by
          apply names.injective
          apply Subtype.ext
          simpa using hr
        change C.graph.Adj (leftName names e) (rightName names e)
        rw [ha,hb]
        exact C.graph.adj_symm hxy
    · rcases he with ⟨hl,_⟩ | ⟨_,hr⟩
      · exact Or.inl hl.symm
      · exact Or.inr hr.symm
    · rcases he with ⟨_,hr⟩ | ⟨hl,_⟩
      · exact Or.inr hr.symm
      · exact Or.inl hl.symm

/-- Incidence edge elements are isolated as graph vertices. The selected
vertex graph is exactly the original forest, with those isolated elements
adjoined by a genuine graph isomorphism. -/
def selectedGraphIso (hD : Laws D) (names : Fin n ≃ Vertex D)
    (hG : ∀ x y, G.Adj x y ↔ Adjacent D (names x).val (names y).val)
    (C : RootedColor G P) :
    (C.graph ⊕g (⊥ : SimpleGraph (Edge D))) ≃g
      Guidance.selectedGraph (colorData names C).vertices (colorData names C).edges where
  toEquiv := names.sumCongr (Equiv.refl (Edge D))
  map_rel_iff' := by
    intro a b
    change Guidance.Step (colorData names C).vertices (colorData names C).edges
      (Sum.map names id a) (Sum.map names id b) ↔ (C.graph ⊕g (⊥ : SimpleGraph (Edge D))).Adj a b
    cases a with
    | inl x =>
      cases b with
      | inl y => exact selected_step_iff hD names hG C x y
      | inr e =>
        simp [Sum.map,Guidance.Step,IsVertex]
    | inr e =>
      cases b <;> simp [Sum.map,Guidance.Step,IsVertex]

theorem selected_acyclic (hD : Laws D) (names : Fin n ≃ Vertex D)
    (hG : ∀ x y, G.Adj x y ↔ Adjacent D (names x).val (names y).val)
    (C : RootedColor G P) :
    (Guidance.selectedGraph (colorData names C).vertices (colorData names C).edges).IsAcyclic :=
  (selectedGraphIso hD names hG C).isAcyclic_iff.mp
    (sumForest_acyclic C.acyclic SimpleGraph.isAcyclic_bot)

end StackSorting.GuidedPathwidth.IncidenceAdapter
