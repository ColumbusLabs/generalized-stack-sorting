import ReplacementBoundaryNeighbors

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} [DecidableEq E]
variable {old : V → E → Prop} {inserted : V → F → Prop} {s t : V} {removed : E}
namespace ReplacementFrame

omit [DecidableEq E] in
theorem unaffected_surviving_boundary_iff (R : ReplacementFrame old inserted s t removed)
    (x : V) (hx : x ∈ R.oldVertices)
    (avoids : ∀ y, SameCutedgeComponent old s t x y → ¬ old y removed)
    (b : CutBoundary E) (hne : b ≠ .cut removed) :
    ComponentTouches (inc := ReplacementIncidence old inserted removed) (s := s) (t := t)
      x (survivingBoundary (F := F) b hne) ↔
    ComponentTouches (inc := old) (s := s) (t := t) x b := by
  have hc := unaffected_component_replacement_iff removed R.removed_cutedge
    R.oldVertices R.newVertices R.anchor R.anchor_incident R.old_support R.new_support R.overlap
    R.inserted_connects R.source_old R.sink_old x hx avoids
  cases b with
  | source => exact hc s
  | sink => exact hc t
  | cut e =>
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,hy,(hc y).mp hxy⟩
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,hy,(hc y).mpr hxy⟩

/-- If a replacement component meets K and touches two distinct surviving old
boundaries, those labels cannot bound any old component. Their actual indices
are forced to be the opposite neighbors of the removed cutedge. -/
theorem old_joint_touch_impossible_of_new_joint_touch
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t)
    (z : V) (hz : z ∈ R.newVertices) (b c : CutBoundary E)
    (hb : BoundaryValid (inc := old) (s := s) (t := t) b)
    (hc : BoundaryValid (inc := old) (s := s) (t := t) c)
    (hbr : b ≠ .cut removed) (hcr : c ≠ .cut removed) (hbc : b ≠ c)
    (hzb : ComponentTouches (inc := ReplacementIncidence old inserted removed) (s := s) (t := t)
      z (survivingBoundary (F := F) b hbr))
    (hzc : ComponentTouches (inc := ReplacementIncidence old inserted removed) (s := s) (t := t)
      z (survivingBoundary (F := F) c hcr)) :
    ∀ x, ComponentTouches (inc := old) (s := s) (t := t) x b →
      ComponentTouches (inc := old) (s := s) (t := t) x c → False := by
  obtain ⟨r,hr⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p (.cut removed)).mpr R.removed_cutedge)
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p b).mpr hb)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp ((mem_boundaryTrace p c).mpr hc)
  obtain ⟨u,hur,hub⟩ := R.old_joint_touch_from_new_boundary z hz b hbr hzb
  obtain ⟨v,hvr,hvc⟩ := R.old_joint_touch_from_new_boundary z hz c hcr hzc
  have hri : r ≠ i := by intro h; exact hbr (hi.symm.trans ((congrArg (fun a => (boundaryTrace p).get a) h.symm).trans hr))
  have hrj : r ≠ j := by intro h; exact hcr (hj.symm.trans ((congrArg (fun a => (boundaryTrace p).get a) h.symm).trans hr))
  have hij : i ≠ j := by intro h; exact hbc (hi.symm.trans ((congrArg (fun a => (boundaryTrace p).get a) h).trans hj))
  have ni := touched_boundary_indices_neighbor p u r i hri (hr.symm ▸ hur) (hi.symm ▸ hub)
  have nj := touched_boundary_indices_neighbor p v r j hrj (hr.symm ▸ hvr) (hj.symm ▸ hvc)
  intro x hxb hxc
  exact distinct_boundary_neighbors_have_no_joint_component p r i j hij ni nj x
    (hi.symm ▸ hxb) (hj.symm ▸ hxc)

/-- Every old vertex in a new two-old-boundary bridge is affected when any
component in that same bridge union meets K. This is uniform over the whole
union, even when its vertices occupy distinct actual components. -/
theorem merged_bridge_old_vertex_touches_removed
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t)
    (z : V) (hz : z ∈ R.newVertices) (b c : CutBoundary E)
    (hb : BoundaryValid (inc := old) (s := s) (t := t) b)
    (hc : BoundaryValid (inc := old) (s := s) (t := t) c)
    (hbr : b ≠ .cut removed) (hcr : c ≠ .cut removed) (hbc : b ≠ c)
    (hzregion : BridgeRegion (inc := ReplacementIncidence old inserted removed) (s := s) (t := t)
      (survivingBoundary (F := F) b hbr) (survivingBoundary (F := F) c hcr) z)
    (x : V) (hx : x ∈ R.oldVertices)
    (hxregion : BridgeRegion (inc := ReplacementIncidence old inserted removed) (s := s) (t := t)
      (survivingBoundary (F := F) b hbr) (survivingBoundary (F := F) c hcr) x) :
    ComponentTouches (inc := old) (s := s) (t := t) x (.cut removed) := by
  classical
  have hbnew := R.survivingBoundary_valid b hbr hb
  have hcnew := R.survivingBoundary_valid c hcr hc
  by_contra hn
  have avoids : ∀ y, SameCutedgeComponent old s t x y → ¬ old y removed :=
    fun y hxy hy => hn ⟨y,hy,hxy⟩
  have hxb := (R.unaffected_surviving_boundary_iff x hx avoids b hbr).mp
    ((hxregion _ hbnew).mpr (Or.inl rfl))
  have hxc := (R.unaffected_surviving_boundary_iff x hx avoids c hcr).mp
    ((hxregion _ hcnew).mpr (Or.inr rfl))
  exact R.old_joint_touch_impossible_of_new_joint_touch p z hz b c hb hc hbr hcr hbc
    ((hzregion _ hbnew).mpr (Or.inl rfl)) ((hzregion _ hcnew).mpr (Or.inr rfl)) x hxb hxc

/-- The affected old part of a merged bridge is the union of precisely the old
removed appendix and the two old exterior bridge regions. -/
theorem affected_two_old_region_support
    (R : ReplacementFrame old inserted s t removed) (p : Path old s t)
    (b c : CutBoundary E)
    (hb : BoundaryValid (inc := old) (s := s) (t := t) b)
    (hc : BoundaryValid (inc := old) (s := s) (t := t) c)
    (hbr : b ≠ .cut removed) (hcr : c ≠ .cut removed) (hbc : b ≠ c)
    (x : V)
    (hr : ComponentTouches (inc := old) (s := s) (t := t) x (.cut removed))
    (hxregion : BridgeRegion (inc := ReplacementIncidence old inserted removed) (s := s) (t := t)
      (survivingBoundary (F := F) b hbr) (survivingBoundary (F := F) c hcr) x) :
    AppendixRegion (inc := old) (s := s) (t := t) removed x ∨
    BridgeRegion (inc := old) (s := s) (t := t) (.cut removed) b x ∨
    BridgeRegion (inc := old) (s := s) (t := t) (.cut removed) c x := by
  classical
  have hsub : ∀ d, BoundaryValid (inc := old) (s := s) (t := t) d →
      ComponentTouches (inc := old) (s := s) (t := t) x d →
      d = .cut removed ∨ d = b ∨ d = c := by
    intro d hd hxd
    by_cases hdr : d = .cut removed
    · exact Or.inl hdr
    have hnew := R.survivingBoundary_touched x d hdr hxd
    rcases (hxregion _ (R.survivingBoundary_valid d hdr hd)).mp hnew with h | h
    · exact Or.inr (Or.inl (survivingBoundary_injective hdr hbr h))
    · exact Or.inr (Or.inr (survivingBoundary_injective hdr hcr h))
  have no_both : ¬ (ComponentTouches (inc := old) (s := s) (t := t) x b ∧
      ComponentTouches (inc := old) (s := s) (t := t) x c) := by
    rintro ⟨hxb,hxc⟩
    have hrv : BoundaryValid (inc := old) (s := s) (t := t) (.cut removed) := R.removed_cutedge
    have hc_eq : c = .cut removed ∨ c = b := by
      rcases boundary_trichotomy p hrv hb with heq | hrb | hbr'
      · exact (hbr heq.symm).elim
      · exact component_third_boundary_eq p x hrv hb hc hrb hr hxb hxc
      · exact (component_third_boundary_eq p x hb hrv hc hbr' hxb hr hxc).elim Or.inr Or.inl
    exact hc_eq.elim hcr (fun h => hbc h.symm)
  by_cases hxb : ComponentTouches (inc := old) (s := s) (t := t) x b
  · have hnc := fun hxc => no_both ⟨hxb,hxc⟩
    refine Or.inr (Or.inl ?_)
    intro d hd
    constructor
    · intro hxd
      rcases hsub d hd hxd with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (hnc (h ▸ hxd)).elim
    · rintro (rfl | rfl)
      · exact hr
      · exact hxb
  by_cases hxc : ComponentTouches (inc := old) (s := s) (t := t) x c
  · refine Or.inr (Or.inr ?_)
    intro d hd
    constructor
    · intro hxd
      rcases hsub d hd hxd with h | h | h
      · exact Or.inl h
      · exact (hxb (h ▸ hxd)).elim
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact hr
      · exact hxc
  · refine Or.inl ?_
    intro d hd
    constructor
    · intro hxd
      rcases hsub d hd hxd with h | h | h
      · exact h
      · exact (hxb (h ▸ hxd)).elim
      · exact (hxc (h ▸ hxd)).elim
    · intro h
      exact h.symm ▸ hr

end ReplacementFrame
end FiniteFlow.Hypergraph
