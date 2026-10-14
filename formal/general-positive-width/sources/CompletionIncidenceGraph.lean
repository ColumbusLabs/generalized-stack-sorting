import CompletionIncidenceRealization

namespace StackSorting.CapturedLinkExtraction.MultiMargin.CompletionIncidence
open SparseEndpointMSO SparseEndpointMSO.Guidance SparseEndpointMSO.FiniteCopy
open SparseEndpointMSO.IncidenceOwnership GraphWidth GraphWidth.Nested
variable {D : Model} {n t k : Nat} {G : Graph n} {T : FinitePort.RootedTree t}
variable (dec : Decomposition G T) (names : Fin n ≃ Vertex D)

def named (u : Fin n) : Actual (D := D) dec := .inl (namedVertex names u)

theorem named_injective : Function.Injective (named dec names) := by
  intro u v h
  exact namedVertex_injective names (Sum.inl.inj h)

theorem vertex_exact (x : Actual (D := D) dec) : vertex dec x ↔ ∃ u, x=named dec names u := by
  cases x with
  | inr e =>
    constructor
    · exact False.elim
    · rintro ⟨u,h⟩; simp [named,namedVertex] at h
  | inl x =>
    cases x with
    | inr e =>
      constructor
      · exact False.elim
      · rintro ⟨u,h⟩
        have he : (Sum.inr e : IncidenceOwnership.Element D) = Sum.inl (names u) :=
          Sum.inl.inj h
        cases he
    | inl v =>
      constructor
      · intro _
        obtain ⟨u,hu⟩ := names.surjective v
        exact ⟨u,congrArg (fun z => Sum.inl (Sum.inl z)) hu.symm⟩
      · intro _; trivial

theorem incidence_vertex (x e : Actual (D := D) dec) (h : incident dec names x e) : vertex dec x := by
  cases x with
  | inr x => exact h.elim
  | inl x =>
    cases e with
    | inl e =>
      cases x with
      | inl x => trivial
      | inr x => exact h.elim
    | inr e =>
      rcases h with rfl | rfl <;> trivial

/-- Exact endpoint rigidity of the actual completed edge carrier. -/
theorem pair_rigid (e : Actual (D := D) dec) (he : edge dec e) {u v a b : Fin n}
    (hne : u ≠ v) (hab : a ≠ b)
    (hu : incident dec names (named dec names u) e)
    (hv : incident dec names (named dec names v) e)
    (ha : incident dec names (named dec names a) e)
    (hb : incident dec names (named dec names b) e) :
    (u=a ∧ v=b) ∨ (u=b ∧ v=a) := by
  cases e with
  | inl e =>
    have huv : namedVertex names u ≠ namedVertex names v :=
      fun h => hne (namedVertex_injective names h)
    have hab' : namedVertex names a ≠ namedVertex names b :=
      fun h => hab (namedVertex_injective names h)
    rcases incident_pair_rigid he huv hab' hu hv ha hb with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨namedVertex_injective names h₁,namedVertex_injective names h₂⟩
    · exact Or.inr ⟨namedVertex_injective names h₁,namedVertex_injective names h₂⟩
  | inr e =>
    have classify : ∀ w, incident dec names (named dec names w) (.inr e) →
        w=e.val.1 ∨ w=e.val.2 := by
      intro w hw
      exact hw.elim (fun h => Or.inl (namedVertex_injective names h))
        (fun h => Or.inr (namedVertex_injective names h))
    rcases classify u hu with hu | hu <;> rcases classify v hv with hv | hv <;>
      rcases classify a ha with ha | ha <;> rcases classify b hb with hb | hb <;>
      simp_all

/-- The inherited physical graph, tested only by original incidence. -/
theorem original_pair (hD : Laws D)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent D (names u).val (names v).val)
    (u v : Fin n) (hne : u ≠ v) :
    (∃ e : IncidenceOwnership.Element D, IsEdge e ∧
      ElementIncident (namedVertex names u) e ∧
      ElementIncident (namedVertex names v) e) ↔ G.Adj u v := by
  constructor
  · rintro ⟨e,he,hu,hv⟩
    cases e with
    | inl e => exact he.elim
    | inr e =>
      apply (hG u v).mpr
      have hn : (names u).val ≠ (names v).val :=
        fun h => hne (names.injective (Subtype.ext h))
      change ((names u).val=e.val.1 ∨ (names u).val=e.val.2) at hu
      change ((names v).val=e.val.1 ∨ (names v).val=e.val.2) at hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact (hn (hu.trans hv.symm)).elim
      · exact (edge_coverage hD _ _).mpr ⟨e,Or.inl ⟨hu.symm,hv.symm⟩⟩
      · exact (edge_coverage hD _ _).mpr ⟨e,Or.inr ⟨hv.symm,hu.symm⟩⟩
      · exact (hn (hu.trans hv.symm)).elim
  · exact incidence_edge_of_named_graph hD names G hG u v

/-- Every and only completed graph pairs have an actual edge object. The
strict ordering orients only the genuine ExtraEdge carrier, never syntax. -/
theorem pair_coverage (hD : Laws D)
    (hG : ∀ u v, G.Adj u v ↔ Adjacent D (names u).val (names v).val)
    (u v : Fin n) (hne : u ≠ v) :
    (∃ e : Actual (D := D) dec, edge dec e ∧ incident dec names (named dec names u) e ∧
      incident dec names (named dec names v) e) ↔
      (GraphWidth.MultiMargin.Completion dec).Adj u v := by
  classical
  constructor
  · rintro ⟨e,he,hu,hv⟩
    cases e with
    | inl e => exact ⟨hne,Or.inl ((original_pair names hD hG u v hne).mp ⟨e,he,hu,hv⟩)⟩
    | inr e =>
      have hu' : u=e.val.1 ∨ u=e.val.2 :=
        hu.elim (fun h => Or.inl (namedVertex_injective names h))
          (fun h => Or.inr (namedVertex_injective names h))
      have hv' : v=e.val.1 ∨ v=e.val.2 :=
        hv.elim (fun h => Or.inl (namedVertex_injective names h))
          (fun h => Or.inr (namedVertex_injective names h))
      rcases hu' with rfl | rfl <;> rcases hv' with hv | hv
      · exact (hne hv.symm).elim
      · simpa only [hv] using e.property.2.1
      · simpa only [hv] using (GraphWidth.MultiMargin.Completion dec).symm e.property.2.1
      · exact (hne hv.symm).elim
  · intro huv
    by_cases hg : G.Adj u v
    · obtain ⟨e,he,hu,hv⟩ := (original_pair names hD hG u v hne).mpr hg
      exact ⟨.inl e,he,hu,hv⟩
    · by_cases ho : u.val<v.val
      · let e : ExtraEdge dec := ⟨(u,v),ho,huv,hg⟩
        exact ⟨.inr e,trivial,Or.inl rfl,Or.inr rfl⟩
      · have ho' : v.val<u.val := by
          have hh : u.val ≠ v.val := fun h => hne (Fin.ext h)
          omega
        let e : ExtraEdge dec := ⟨(v,u),ho',(GraphWidth.MultiMargin.Completion dec).symm huv,
          fun h => hg (G.symm h)⟩
        exact ⟨.inr e,trivial,Or.inr rfl,Or.inl rfl⟩

/-- Empty actual vertex universes cannot conceal synthetic objects. -/
theorem no_extra_zero {G0 : Graph 0} {T0 : FinitePort.RootedTree t}
    (dec0 : Decomposition G0 T0) (e : ExtraEdge dec0) : False :=
  Fin.elim0 e.val.1

/-- No root pair is available at zero colors; capture forces the actual
completion to contain no extra edges. -/
theorem no_extra_zero_colors (C : Colors D 0) (hcap : Captured dec names C)
    (e : ExtraEdge dec) : False := by
  obtain ⟨q,_⟩ := extra_has_candidate names C hcap e
  exact Fin.elim0 q.1

#print axioms pair_rigid
#print axioms pair_coverage
#print axioms no_extra_zero
#print axioms no_extra_zero_colors
end StackSorting.CapturedLinkExtraction.MultiMargin.CompletionIncidence
