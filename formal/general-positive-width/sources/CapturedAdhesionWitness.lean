import CapturedLinkSelection

namespace StackSorting.CapturedLinkExtraction
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership GraphWidth SameVertexForest
open ConnectedConeNormalization
variable {D : Model} {n k : Nat}

/-- Capture is expressed by actual colored-root reachability in the input
incidence structure. It is not an assumed parent or preorder formula. -/
def AdhesionsCaptured (names : Fin n ≃ Vertex D) (C : Colors D k)
    (G : Graph n) (O : RankedOrder n) : Prop :=
  ∀ a, (∃ u, RegionAdhesion G O a u) → ∃ z,
    ∀ u, RegionAdhesion G O a u → ∃ i, ColorRoot C i z (namedVertex names u)

theorem filledAdhesions_symm (G : Graph n) (O : RankedOrder n) {u v}
    (h : FilledAdhesionsAdj G O u v) : FilledAdhesionsAdj G O v u := by
  rcases h with ⟨hne,he | ⟨a,hu,hv⟩⟩
  · exact ⟨Ne.symm hne,Or.inl (G.symm he)⟩
  · exact ⟨Ne.symm hne,Or.inr ⟨a,hv,hu⟩⟩

/-- The accepted simple S/M ownership theorem supplies actual original edge
elements from a genuine named graph equivalence. -/
theorem incidence_edge_of_named_graph (hD : Laws D) (names : Fin n ≃ Vertex D)
    (G : Graph n)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent D (names u).val (names v).val)
    (u v) (h : G.Adj u v) :
    ∃ e, IsEdge e ∧ ElementIncident (namedVertex names u) e ∧
      ElementIncident (namedVertex names v) e := by
  obtain ⟨e,he | he⟩ := (edge_coverage hD _ _).mp ((hG u v).mp h)
  · exact ⟨.inr e,trivial,Or.inl he.1.symm,Or.inr he.2.symm⟩
  · exact ⟨.inr e,trivial,Or.inr he.2.symm,Or.inl he.1.symm⟩

/-- The checked sane connector theorem supplies the whole availability
premise, including original edges and adhesion-only synthetic links. -/
theorem normalized_parent_available (names : Fin n ≃ Vertex D) (C : Colors D k)
    (G : Graph n) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (hi : ∀ u v, G.Adj u v → ∃ e, IsEdge e ∧
      ElementIncident (namedVertex names u) e ∧ ElementIncident (namedVertex names v) e)
    (hc : AdhesionsCaptured names C G (normalizedOrder G O)) (u v)
    (hp : ParentAdj (normalizedOrder G O) u v) : Available names C u v := by
  have hf : FilledAdhesionsAdj G (normalizedOrder G O) u v := by
    rcases hp with ⟨hne,hp⟩ | ⟨hne,hp⟩
    · apply filledAdhesions_symm G _
      exact hp ▸ normalized_parent_adhesion_filled G O he hne
    · exact hp ▸ normalized_parent_adhesion_filled G O he hne
  rcases hf.2 with hadj | ⟨a,hu,hv⟩
  · exact Or.inl (hi u v hadj)
  · obtain ⟨z,hz⟩ := hc a ⟨u,hu⟩
    obtain ⟨i,hi⟩ := hz u hu
    obtain ⟨j,hj⟩ := hz v hv
    exact Or.inr ⟨i,j,z,hi,hj⟩

/-- Construct an actual supported fixed-arity original-vocabulary tuple and
prove its strict earlier formula on every original vertex pair. Constants and
syntax depend only on the guidance-color count k. No binary parent parameter
is present in the syntax or the tuple. -/
theorem exists_supported_earlier_of_captured_adhesions (hD : Laws D)
    (names : Fin n ≃ Vertex D) (C : Colors D k) (hC : C.Valid)
    (G : Graph n) (O : RankedOrder n)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (hi : ∀ u v, G.Adj u v → ∃ e, IsEdge e ∧
      ElementIncident (namedVertex names u) e ∧ ElementIncident (namedVertex names v) e)
    (hc : AdhesionsCaptured names C G (normalizedOrder G O)) :
    ∃ X : Fin (parameterCount k * 3) → Nat → Prop,
      CanonicalChoice.SupportedTuple D X ∧ ∀ u v,
        Eval D (sparseEarlier k) (Fin.cases (names u).val (fun _ => (names v).val)) X ↔
          (normalizedOrder G O).rel u v := by
  let S := forestSelection names C (normalizedOrder G O)
  refine ⟨originalSets hD (chosenSets C S),originalSets_supported hD _,?_⟩
  intro u v
  exact sparseEarlier_forest_exact hD names C hC (normalizedOrder G O)
    (normalized_parent_available names C G O he hi hc) u v

theorem named_graph_exists_supported_earlier (hD : Laws D)
    (names : Fin n ≃ Vertex D) (C : Colors D k) (hC : C.Valid)
    (G : Graph n) (O : RankedOrder n)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent D (names u).val (names v).val)
    (he : ∀ {u v}, G.Adj u v → O.rel u v ∨ O.rel v u)
    (hc : AdhesionsCaptured names C G (normalizedOrder G O)) :
    ∃ X : Fin (parameterCount k * 3) → Nat → Prop,
      CanonicalChoice.SupportedTuple D X ∧ ∀ u v,
        Eval D (sparseEarlier k) (Fin.cases (names u).val (fun _ => (names v).val)) X ↔
          (normalizedOrder G O).rel u v :=
  exists_supported_earlier_of_captured_adhesions hD names C hC G O he
    (incidence_edge_of_named_graph hD names G hG) hc

#print axioms named_graph_exists_supported_earlier
#print axioms normalized_parent_available
#print axioms exists_supported_earlier_of_captured_adhesions
end StackSorting.CapturedLinkExtraction
