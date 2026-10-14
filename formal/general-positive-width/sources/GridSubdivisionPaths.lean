import UnitGridIntersections

namespace StackSorting.GraphWidth.UCurve

theorem GridArc.onPath_cases {p q x : Point} (A : GridArc p q)
    (h : A.OnPath x) : x = p ∨ x = q ∨ A.Interior x := by
  obtain ⟨a, ha, hx⟩ := h
  by_cases hz : a = 0
  · left; subst a; exact hx.symm.trans A.first
  by_cases hl : a = A.length
  · right; left; subst a; exact hx.symm.trans A.last
  · exact Or.inr (Or.inr ⟨a, by omega, by omega, hx⟩)

theorem GridSubdivision.onPath_vertex_endpoint {n} {G : Graph n}
    (S : GridSubdivision G) (e : OrderedEdge G) (v : Fin n)
    (h : (S.route e).OnPath (S.point v)) : v = e.low ∨ v = e.high := by
  rcases (S.route e).onPath_cases h with hl | hh | hi
  · exact Or.inl (S.injective hl)
  · exact Or.inr (S.injective hh)
  · exact False.elim (S.avoids_vertices e (S.point v) hi v rfl)

/-- Two different source edges can share a lattice point only when it is
the image of a source vertex that is an endpoint of both edges. -/
theorem GridSubdivision.distinct_routes_meet_at_vertices {n} {G : Graph n}
    (S : GridSubdivision G) (e f : OrderedEdge G) (hne : e ≠ f) {x : Point}
    (he : (S.route e).OnPath x) (hf : (S.route f).OnPath x) :
    ∃ v : Fin n, x = S.point v ∧ (v = e.low ∨ v = e.high) ∧
      (v = f.low ∨ v = f.high) := by
  rcases (S.route e).onPath_cases he with hl | hh | hi
  · refine ⟨e.low, hl, Or.inl rfl, ?_⟩
    exact S.onPath_vertex_endpoint f e.low (hl ▸ hf)
  · refine ⟨e.high, hh, Or.inr rfl, ?_⟩
    exact S.onPath_vertex_endpoint f e.high (hh ▸ hf)
  · rcases (S.route f).onPath_cases hf with hl | hh | hj
    · exact False.elim (S.avoids_vertices e x hi f.low hl)
    · exact False.elim (S.avoids_vertices e x hi f.high hh)
    · exact False.elim (hne (S.disjoint e f x hi hj))

/-- Two distinct simple edges have at most one common source endpoint. -/
theorem OrderedEdge.two_common_endpoints {n} {G : Graph n}
    {e f : OrderedEdge G} {u v : Fin n} (huv : u ≠ v)
    (heu : u = e.low ∨ u = e.high) (hev : v = e.low ∨ v = e.high)
    (hfu : u = f.low ∨ u = f.high) (hfv : v = f.low ∨ v = f.high) : e = f := by
  have ho := e.ordered
  have hp := f.ordered
  rcases heu with heu | heu <;> rcases hev with hev | hev <;>
    rcases hfu with hfu | hfu <;> rcases hfv with hfv | hfv
  all_goals try { exfalso; apply huv; exact heu.trans hev.symm }
  all_goals try { exfalso; apply huv; exact hfu.trans hfv.symm }
  all_goals first
    | exact OrderedEdge.ext (heu.symm.trans hfu) (hev.symm.trans hfv)
    | exact OrderedEdge.ext (hev.symm.trans hfv) (heu.symm.trans hfu)
    | have h1 := congrArg Fin.val (heu.symm.trans hfu)
      have h2 := congrArg Fin.val (hev.symm.trans hfv)
      omega

/-- Two different source routes cannot contain the same two lattice
points. In particular they cannot share a whole unit segment. -/
theorem GridSubdivision.two_points_determine_edge {n} {G : Graph n}
    (S : GridSubdivision G) (e f : OrderedEdge G) {x y : Point} (hxy : x ≠ y)
    (hex : (S.route e).OnPath x) (hey : (S.route e).OnPath y)
    (hfx : (S.route f).OnPath x) (hfy : (S.route f).OnPath y) : e = f := by
  by_cases h : e = f
  · exact h
  obtain ⟨u, hx, heu, hfu⟩ := S.distinct_routes_meet_at_vertices e f h hex hfx
  obtain ⟨v, hy, hev, hfv⟩ := S.distinct_routes_meet_at_vertices e f h hey hfy
  have huv : u ≠ v := by intro he; apply hxy; exact hx.trans ((congrArg S.point he).trans hy.symm)
  exact OrderedEdge.two_common_endpoints huv heu hev hfu hfv

/-- Intersection of unit segments in any ordered realization yields a
shared source endpoint for two distinct source routes. This does not yet
construct a rotation map or its faces. -/
theorem GridSubdivision.realized_segment_common_vertex {n} {G : Graph n}
    (S : GridSubdivision G) {α : Type} [LE α] [LT α] (C : OrderedCoordinates α)
    (e f : OrderedEdge G) (hne : e ≠ f) {a b : Nat} {x y : α}
    (ha : a < (S.route e).length) (hb : b < (S.route f).length)
    (he : InCoordinateBox C ((S.route e).atPoint a) ((S.route e).atPoint (a+1)) x y)
    (hf : InCoordinateBox C ((S.route f).atPoint b) ((S.route f).atPoint (b+1)) x y) :
    ∃ v : Fin n, (v = e.low ∨ v = e.high) ∧ (v = f.low ∨ v = f.high) := by
  have h := realized_unit_segments_meet_endpoints C ((S.route e).step a ha)
    ((S.route f).step b hb) he hf
  have ea : (S.route e).OnPath ((S.route e).atPoint a) := ⟨a, by omega, rfl⟩
  have ea1 : (S.route e).OnPath ((S.route e).atPoint (a+1)) := ⟨a+1, by omega, rfl⟩
  have fb : (S.route f).OnPath ((S.route f).atPoint b) := ⟨b, by omega, rfl⟩
  have fb1 : (S.route f).OnPath ((S.route f).atPoint (b+1)) := ⟨b+1, by omega, rfl⟩
  rcases h with h | h | h | h
  · obtain ⟨v, _, hv, hw⟩ := S.distinct_routes_meet_at_vertices e f hne ea (h ▸ fb)
    exact ⟨v, hv, hw⟩
  · obtain ⟨v, _, hv, hw⟩ := S.distinct_routes_meet_at_vertices e f hne ea (h ▸ fb1)
    exact ⟨v, hv, hw⟩
  · obtain ⟨v, _, hv, hw⟩ := S.distinct_routes_meet_at_vertices e f hne ea1 (h ▸ fb)
    exact ⟨v, hv, hw⟩
  · obtain ⟨v, _, hv, hw⟩ := S.distinct_routes_meet_at_vertices e f hne ea1 (h ▸ fb1)
    exact ⟨v, hv, hw⟩

end StackSorting.GraphWidth.UCurve
