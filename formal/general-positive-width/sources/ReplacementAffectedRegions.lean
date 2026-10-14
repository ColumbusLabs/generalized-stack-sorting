import ReplacementComponentCorrespondence
import CutedgeRegionLocalization

namespace FiniteFlow.Hypergraph
variable {V E F : Type*} {old : V → E → Prop} {inserted : V → F → Prop} {s t : V}

/- Primitive replacement hypotheses, retaining actual vertex and edge names.
No component correspondence, pathwidth witness, or replacement endpoint is a field. -/
structure ReplacementFrame (old : V → E → Prop) (inserted : V → F → Prop)
    (s t : V) (removed : E) where
  oldVertices : Set V
  newVertices : Set V
  anchor : V
  anchor_incident : old anchor removed
  old_support : ∀ x e, old x e → x ∈ oldVertices
  new_support : ∀ x f, inserted x f → x ∈ newVertices
  overlap : ∀ x, x ∈ oldVertices → x ∈ newVertices → old x removed
  source_old : s ∈ oldVertices
  sink_old : t ∈ oldVertices
  removed_cutedge : Cutedge old s t removed
  inserted_connects : ∀ a b, old a removed → old b removed → Nonempty (HWalk inserted a b)

namespace ReplacementFrame
variable {removed : E} (R : ReplacementFrame old inserted s t removed)

/- Embed any boundary except the removed cutedge, preserving source and sink. -/
def survivingBoundary (b : CutBoundary E) (h : b ≠ .cut removed) :
    CutBoundary ({e : E // e ≠ removed} ⊕ F) :=
  match b with
  | .source => .source
  | .sink => .sink
  | .cut e => .cut (.inl ⟨e,fun he => h (congrArg CutBoundary.cut he)⟩)

theorem survivingBoundary_not_inserted (b : CutBoundary E) (h : b ≠ .cut removed) (f : F) :
    survivingBoundary (F := F) b h ≠ .cut (.inr f) := by
  cases b <;> simp [survivingBoundary]

include R in
theorem survivingBoundary_valid (b : CutBoundary E) (h : b ≠ .cut removed)
    (hb : BoundaryValid (inc := old) (s := s) (t := t) b) :
    BoundaryValid (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (survivingBoundary (F := F) b h) := by
  cases b with
  | source => trivial
  | sink => trivial
  | cut e =>
    exact old_cutedge_replacement removed R.oldVertices R.newVertices R.anchor R.anchor_incident
      R.old_support R.new_support R.overlap R.source_old R.sink_old
      ⟨e,fun he => h (congrArg CutBoundary.cut he)⟩ hb

include R in
theorem survivingBoundary_touched (x : V) (b : CutBoundary E) (h : b ≠ .cut removed)
    (hx : ComponentTouches (inc := old) (s := s) (t := t) x b) :
    ComponentTouches (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) x (survivingBoundary (F := F) b h) := by
  cases b with
  | source => exact old_component_survives_replacement removed R.removed_cutedge R.inserted_connects hx
  | sink => exact old_component_survives_replacement removed R.removed_cutedge R.inserted_connects hx
  | cut e =>
    obtain ⟨y,hy,hxy⟩ := hx
    exact ⟨y,hy,old_component_survives_replacement removed R.removed_cutedge R.inserted_connects hxy⟩

/- If all touched new boundaries are inserted identifiers, every old vertex
in that component was an appendix of the removed edge. Ambient new vertices
are allowed: only an actual old walk from x to the source is required. -/
include R in
theorem inserted_only_region_old_appendix (x : V) (to_source : Nonempty (HWalk old x s))
    (inserted_only : ∀ b, BoundaryValid (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) b →
      ComponentTouches (inc := ReplacementIncidence old inserted removed) (s := s) (t := t) x b →
      ∃ f, b = .cut (.inr f)) :
    AppendixRegion (inc := old) (s := s) (t := t) removed x := by
  have only_removed : ∀ b, BoundaryValid (inc := old) (s := s) (t := t) b →
      ComponentTouches (inc := old) (s := s) (t := t) x b → b = .cut removed := by
    intro b hb hxb
    by_contra hne
    obtain ⟨f,hf⟩ := inserted_only (survivingBoundary (F := F) b hne)
      (R.survivingBoundary_valid b hne hb) (R.survivingBoundary_touched x b hne hxb)
    exact survivingBoundary_not_inserted b hne f hf
  have hex : ∃ b, BoundaryValid (inc := old) (s := s) (t := t) b ∧
      ComponentTouches (inc := old) (s := s) (t := t) x b := by
    obtain ⟨w⟩ := to_source
    rcases component_reaches_target_or_cutedge (s := s) (t := t) w with hs | hc
    · exact ⟨.source,trivial,hs⟩
    · obtain ⟨e,y,he,hy,hxy⟩ := hc
      exact ⟨.cut e,he,y,hy,hxy⟩
  obtain ⟨b,hb,hxb⟩ := hex
  have hr : ComponentTouches (inc := old) (s := s) (t := t) x (.cut removed) :=
    only_removed b hb hxb ▸ hxb
  intro c hc
  exact ⟨only_removed c hc,fun h => h.symm ▸ hr⟩

/- Old vertices of a new appendix belong to the removed old appendix union. -/
include R in
theorem inserted_appendix_old_support (x : V) (to_source : Nonempty (HWalk old x s)) (f : F)
    (hregion : AppendixRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (.inr f) x) :
    AppendixRegion (inc := old) (s := s) (t := t) removed x := by
  apply R.inserted_only_region_old_appendix x to_source
  intro b hb hxb
  exact ⟨f,(hregion b hb).mp hxb⟩

/- Old vertices of a bridge between two inserted boundaries also belong to
that same old appendix union. This supplies the interior-support step of 5.8. -/
include R in
theorem inserted_bridge_old_support (x : V) (to_source : Nonempty (HWalk old x s)) (f g : F)
    (hregion : BridgeRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (.cut (.inr f)) (.cut (.inr g)) x) :
    AppendixRegion (inc := old) (s := s) (t := t) removed x := by
  apply R.inserted_only_region_old_appendix x to_source
  intro b hb hxb
  rcases (hregion b hb).mp hxb with h | h
  · exact ⟨f,h⟩
  · exact ⟨g,h⟩

theorem survivingBoundary_injective {a b : CutBoundary E}
    (ha : a ≠ .cut removed) (hb : b ≠ .cut removed)
    (heq : survivingBoundary (F := F) a ha = survivingBoundary (F := F) b hb) : a = b := by
  cases a <;> cases b <;> simp_all [survivingBoundary]

/- Touching an inserted edge forces the old component to meet the removed
edge. This supplies affectedness from an actual new boundary touch. -/
theorem inserted_touch_implies_old_removed_touch (x : V) (hx : x ∈ R.oldVertices) (f : F)
    (hf : ComponentTouches (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) x (.cut (.inr f))) :
    ComponentTouches (inc := old) (s := s) (t := t) x (.cut removed) := by
  classical
  by_contra hn
  have avoids : ∀ y, SameCutedgeComponent old s t x y → ¬ old y removed := by
    intro y hxy hy
    exact hn ⟨y,hy,hxy⟩
  exact unaffected_component_no_inserted_touch removed R.oldVertices R.newVertices R.anchor
    R.anchor_incident R.old_support R.new_support R.overlap R.source_old R.sink_old x hx avoids f hf

/- For a new exterior bridge between a surviving old boundary and an inserted
cutedge, each old vertex comes from the removed appendix or the old bridge
between that boundary and the removed edge. This is actual support transport. -/
theorem exterior_bridge_old_support (x : V) (hx : x ∈ R.oldVertices)
    (b : CutBoundary E) (hne : b ≠ .cut removed) (f : F)
    (hf : Cutedge (ReplacementIncidence old inserted removed) s t (.inr f))
    (hregion : BridgeRegion (inc := ReplacementIncidence old inserted removed)
      (s := s) (t := t) (survivingBoundary (F := F) b hne) (.cut (.inr f)) x) :
    AppendixRegion (inc := old) (s := s) (t := t) removed x ∨
      BridgeRegion (inc := old) (s := s) (t := t) (.cut removed) b x := by
  classical
  have htouch := (hregion (.cut (.inr f)) hf).mpr (Or.inr rfl)
  have hr := R.inserted_touch_implies_old_removed_touch x hx f htouch
  have hsub : ∀ c, BoundaryValid (inc := old) (s := s) (t := t) c →
      ComponentTouches (inc := old) (s := s) (t := t) x c → c = .cut removed ∨ c = b := by
    intro c hc hxc
    by_cases heq : c = .cut removed
    · exact Or.inl heq
    · have hnew := R.survivingBoundary_touched x c heq hxc
      have hv := R.survivingBoundary_valid c heq hc
      rcases (hregion _ hv).mp hnew with hb | hf'
      · exact Or.inr (survivingBoundary_injective heq hne hb)
      · exact (survivingBoundary_not_inserted c heq f hf').elim
  by_cases hb : ComponentTouches (inc := old) (s := s) (t := t) x b
  · refine Or.inr ?_
    intro c hc
    constructor
    · exact hsub c hc
    · rintro (rfl | rfl)
      · exact hr
      · exact hb
  · refine Or.inl ?_
    intro c hc
    constructor
    · intro hxc
      rcases hsub c hc hxc with h | h
      · exact h
      · exact (hb (h ▸ hxc)).elim
    · intro h
      exact h.symm ▸ hr

end ReplacementFrame
end FiniteFlow.Hypergraph
