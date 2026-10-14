import GuidanceIncidenceGraph

namespace StackSorting.GuidedPathwidth.IncidenceAdapter
open SparseEndpointMSO SparseEndpointMSO.IncidenceOwnership
variable {D : Model} {n c : Nat} {G : SimpleGraph (Fin n)} {P : Set (Fin n)}

private theorem sum_empty_reachable_iff {V W : Type} (H : SimpleGraph V) (x y : V) :
    (H ⊕g (⊥ : SimpleGraph W)).Reachable (.inl x) (.inl y) ↔ H.Reachable x y := by
  constructor
  · rintro ⟨w⟩
    let f : (H ⊕g (⊥ : SimpleGraph W)) →g H := {
      toFun := Sum.elim id (fun _ => x)
      map_rel' := by intro a b h; cases a <;> cases b <;> simp_all }
    exact ⟨w.map f⟩
  · intro h
    exact h.map (SimpleGraph.Embedding.sumInl (H := (⊥ : SimpleGraph W))).toHom

theorem selected_reachable_iff (hD : Laws D) (names : Fin n ≃ Vertex D)
    (hG : ∀ x y, G.Adj x y ↔ Adjacent D (names x).val (names y).val)
    (C : RootedColor G P) (x y : Fin n) :
    (Guidance.selectedGraph (colorData names C).vertices (colorData names C).edges).Reachable
      (namedVertex names x) (namedVertex names y) ↔ C.graph.Reachable x y := by
  exact (SimpleGraph.Iso.reachable_iff (φ := selectedGraphIso hD names hG C)
    (u := Sum.inl x) (v := Sum.inl y)).trans (sum_empty_reachable_iff C.graph x y)

/-- Exact incidence root relation, with all selected/root guards retained. -/
theorem rootRelation_iff (hD : Laws D) (names : Fin n ≃ Vertex D)
    (hG : ∀ x y, G.Adj x y ↔ Adjacent D (names x).val (names y).val)
    (C : RootedColor G P) (x r : Fin n) :
    Guidance.RootRelation (colorData names C).vertices (colorData names C).edges
      (colorData names C).roots (namedVertex names x) (namedVertex names r) ↔
    r ∈ C.roots ∧ x ∈ C.selected ∧ r ∈ C.selected ∧ C.graph.Reachable x r := by
  unfold Guidance.RootRelation Guidance.Connected
  rw [Guidance.filteredGraph_none]
  change (colorData names C).roots (namedVertex names r) ∧
    (colorData names C).vertices (namedVertex names x) ∧
    (colorData names C).vertices (namedVertex names r) ∧
    (Guidance.selectedGraph (colorData names C).vertices (colorData names C).edges).Reachable
      (namedVertex names x) (namedVertex names r) ↔ _
  rw [color_roots_named,color_vertices_named,color_vertices_named,
    selected_reachable_iff hD names hG C]

theorem color_valid (hD : Laws D) (names : Fin n ≃ Vertex D)
    (hG : ∀ x y, G.Adj x y ↔ Adjacent D (names x).val (names y).val)
    (C : RootedColor G P) : (colorData names C).Valid := by
  refine ⟨⟨color_typed names C,?_⟩,selected_acyclic hD names hG C⟩
  intro a ha
  cases a with
  | inr e => exact ha.elim
  | inl v =>
    let x := names.symm v
    have hx : x ∈ C.selected := ha
    obtain ⟨r,hr,hu⟩ := C.uniqueRoot x hx
    have hv : namedVertex names x = Sum.inl v := by
      change Sum.inl (names (names.symm v)) = Sum.inl v
      rw [names.apply_symm_apply]
    refine ⟨namedVertex names r,?_,?_⟩
    · rw [← hv]
      exact (rootRelation_iff hD names hG C x r).mpr
        ⟨hr.1,hx,C.rootSelected hr.1,hr.2⟩
    · intro b hb
      cases b with
      | inr e => exact hb.1.elim
      | inl w =>
        have hw : Guidance.RootRelation (colorData names C).vertices
            (colorData names C).edges (colorData names C).roots
            (namedVertex names x) (namedVertex names (names.symm w)) := by
          simpa only [namedVertex,Equiv.apply_symm_apply,x] using hb
        have hh := (rootRelation_iff hD names hG C x (names.symm w)).mp hw
        have he : names.symm w = r := hu _ ⟨hh.1,hh.2.2.2⟩
        apply congrArg Sum.inl
        rw [← names.apply_symm_apply w,he]

def colors (names : Fin n ≃ Vertex D) (C : Fin c → RootedColor G P) : Guidance.Colors D c :=
  fun i => colorData names (C i)

theorem colors_valid (hD : Laws D) (names : Fin n ≃ Vertex D)
    (hG : ∀ x y, G.Adj x y ↔ Adjacent D (names x).val (names y).val)
    (C : Fin c → RootedColor G P) : (colors names C).Valid :=
  fun i => color_valid hD names hG (C i)

theorem colors_rootRelation_iff (hD : Laws D) (names : Fin n ≃ Vertex D)
    (hG : ∀ x y, G.Adj x y ↔ Adjacent D (names x).val (names y).val)
    (C : Fin c → RootedColor G P) (i : Fin c) (x r : Fin n) :
    Guidance.RootRelation ((colors names C) i).vertices ((colors names C) i).edges
      ((colors names C) i).roots (namedVertex names x) (namedVertex names r) ↔
    r ∈ (C i).roots ∧ x ∈ (C i).selected ∧ r ∈ (C i).selected ∧
      (C i).graph.Reachable x r := rootRelation_iff hD names hG (C i) x r

/-- Actual nonempty bag capture is transported to the incidence carrier with
exactly the same palette and one named original capturing vertex. -/
theorem capture_to_incidence (hD : Laws D) (names : Fin n ≃ Vertex D)
    (hG : ∀ x y, G.Adj x y ↔ Adjacent D (names x).val (names y).val)
    (C : Fin c → RootedColor G P) {B : Set (Fin n)} (hB : ForestCaptures C B) :
    B.Nonempty → ∃ z : Element D, ∀ r ∈ B, ∃ i,
      Guidance.RootRelation ((colors names C) i).vertices ((colors names C) i).edges
        ((colors names C) i).roots z (namedVertex names r) := by
  intro hb
  obtain ⟨x,hx⟩ := hB hb
  refine ⟨namedVertex names x,?_⟩
  intro r hr
  obtain ⟨i,hi⟩ := hx r hr
  exact ⟨i,(colors_rootRelation_iff hD names hG C i x r).mpr hi⟩

#print axioms colors_valid
#print axioms colors_rootRelation_iff
#print axioms capture_to_incidence
end StackSorting.GuidedPathwidth.IncidenceAdapter
