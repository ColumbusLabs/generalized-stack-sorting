import BoundaryTraceAdjacency

namespace FiniteFlow.Hypergraph
variable {V E : Type*} {inc : V → E → Prop} {s t : V}

/-- Region predicates name actual cutedge components by their boundary touches. -/
def AppendixRegion (e : E) (x : V) : Prop :=
  ∀ b, BoundaryValid (inc := inc) (s := s) (t := t) b →
    (ComponentTouches (inc := inc) (s := s) (t := t) x b ↔ b = .cut e)

def BridgeRegion (a b : CutBoundary E) (x : V) : Prop :=
  ∀ c, BoundaryValid (inc := inc) (s := s) (t := t) c →
    (ComponentTouches (inc := inc) (s := s) (t := t) x c ↔ c = a ∨ c = b)

theorem componentTouches_congr {x y : V}
    (hxy : SameCutedgeComponent inc s t x y) (b : CutBoundary E) :
    ComponentTouches (inc := inc) (s := s) (t := t) x b ↔
      ComponentTouches (inc := inc) (s := s) (t := t) y b := by
  have hyx := sameCutedgeComponent_symm inc s t hxy
  cases b with
  | source => exact ⟨sameCutedgeComponent_trans inc s t hyx,
      sameCutedgeComponent_trans inc s t hxy⟩
  | sink => exact ⟨sameCutedgeComponent_trans inc s t hyx,
      sameCutedgeComponent_trans inc s t hxy⟩
  | cut e =>
    constructor
    · rintro ⟨z,hz,hxz⟩
      exact ⟨z,hz,sameCutedgeComponent_trans inc s t hyx hxz⟩
    · rintro ⟨z,hz,hyz⟩
      exact ⟨z,hz,sameCutedgeComponent_trans inc s t hxy hyz⟩

/-- Every whole noncut hyperedge stays in the appendix region of any one of its
incident vertices. No pairwise-coverage shortcut is used. -/
theorem noncut_edge_appendix_localized {e f : E} {x : V}
    (hf : ¬ Cutedge inc s t f) (hx : inc x f)
    (hregion : AppendixRegion (inc := inc) (s := s) (t := t) e x) :
    ∀ y, inc y f → AppendixRegion (inc := inc) (s := s) (t := t) e y := by
  intro y hy b hb
  have hxy := sameCutedgeComponent_of_noncut_edge inc s t hx hy hf
  exact (componentTouches_congr hxy b).symm.trans (hregion b hb)

theorem noncut_edge_bridge_localized {f : E} {x : V} {a b : CutBoundary E}
    (hf : ¬ Cutedge inc s t f) (hx : inc x f)
    (hregion : BridgeRegion (inc := inc) (s := s) (t := t) a b x) :
    ∀ y, inc y f → BridgeRegion (inc := inc) (s := s) (t := t) a b y := by
  intro y hy c hc
  have hxy := sameCutedgeComponent_of_noncut_edge inc s t hx hy hf
  exact (componentTouches_congr hxy c).symm.trans (hregion c hc)

/-- A vertex in an appendix can occur in no different cutedge separator. -/
theorem appendix_incident_cutedge_eq {e f : E} {x : V}
    (hregion : AppendixRegion (inc := inc) (s := s) (t := t) e x)
    (hf : Cutedge inc s t f) (hxf : inc x f) : f = e := by
  have heq := (hregion (.cut f) hf).mp
    ⟨x,hxf,sameCutedgeComponent_refl inc s t x⟩
  exact CutBoundary.cut.inj heq

/-- Bridge vertices appear in cutedge separators only at the two endpoints.
This is the region-overlap fact needed for the finite bag-chain seams. -/
theorem bridge_incident_cutedge_endpoint {a b : CutBoundary E} {f : E} {x : V}
    (hregion : BridgeRegion (inc := inc) (s := s) (t := t) a b x)
    (hf : Cutedge inc s t f) (hxf : inc x f) : .cut f = a ∨ .cut f = b :=
  (hregion (.cut f) hf).mp ⟨x,hxf,sameCutedgeComponent_refl inc s t x⟩

end FiniteFlow.Hypergraph
