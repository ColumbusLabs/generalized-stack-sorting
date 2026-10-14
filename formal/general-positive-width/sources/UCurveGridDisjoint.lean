import UCurveGridArcs

namespace StackSorting.GraphWidth.UCurve

theorem sourcePoint_exists {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {x : Vertex tokens events} (hx : x ∈ vertices D) :
    ∃ q : Node D, sourcePoint D q = x.point D := by
  let q : Node D := ⟨(vertices D).idxOf x, List.idxOf_lt_length_of_mem hx⟩
  have hq : nodeVertex D q = x := List.getElem_idxOf _
  exact ⟨q, congrArg (fun v => v.point D) hq⟩

theorem curveSourceArc_positive_interior {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {i j : Node D}
    (h : Consecutive (curveNodes D v) i j) {p : Point}
    (hp : (curveSourceArc D h).Interior p) : 0 < p.depth := by
  have hc := (curveSourceArc_interior D h hp).1
  have hpos := D.positive v
  have hne := curveSourceArc_avoids_vertices D h hp
  apply Nat.pos_of_ne_zero
  intro hz
  rcases hc with ⟨ht, _⟩ | ⟨_, _, hd⟩
  · obtain hl | hr := ht
    · apply hne (anchor D (E.left v))
      simp only [sourcePoint, nodeVertex_anchor, Vertex.point, endpointPoint]
      cases p
      simp_all
    · apply hne (anchor D (E.right v))
      simp only [sourcePoint, nodeVertex_anchor, Vertex.point, endpointPoint]
      cases p
      simp_all
  · omega

/-- Shared open grid points of two source arcs force the same oriented edge. -/
theorem curveSourceArc_interiors_unique {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {u v : Fin tokens} {a b c d : Node D}
    (hab : Consecutive (curveNodes D u) a b)
    (hcd : Consecutive (curveNodes D v) c d) {p : Point}
    (hp : (curveSourceArc D hab).Interior p)
    (hq : (curveSourceArc D hcd).Interior p) : a = c ∧ b = d := by
  obtain ⟨hpu, ha, hb⟩ := curveSourceArc_interior D hab hp
  obtain ⟨hpv, hc, hd⟩ := curveSourceArc_interior D hcd hq
  by_cases he : u = v
  · subst v
    exact hab.open_interval_unique (nodePosition D u) (curveNodes_sorted D u)
      (fun i hi j hj hh => nodePosition_injective_on_curve D
        ((mem_curveNodes D u i).mp hi) ((mem_curveNodes D u j).mp hj) hh)
      hcd ⟨ha, hb⟩ ⟨hc, hd⟩
  · obtain ⟨x, hx, hxp, _, _⟩ := intersection_vertex D he hpu hpv
    obtain ⟨q, hq⟩ := sourcePoint_exists D hx
    exact False.elim (curveSourceArc_avoids_vertices D hab hp q (hxp.symm.trans hq.symm))

/-- Every integer point on a unit segment is one of its two endpoints. -/
def OnUnitSegment (p q x : Point) : Prop :=
  (p.time = q.time ∧ x.time = p.time ∧
    ((p.depth ≤ x.depth ∧ x.depth ≤ q.depth) ∨
      (q.depth ≤ x.depth ∧ x.depth ≤ p.depth))) ∨
  (p.depth = q.depth ∧ x.depth = p.depth ∧
    ((p.time ≤ x.time ∧ x.time ≤ q.time) ∨
      (q.time ≤ x.time ∧ x.time ≤ p.time)))

theorem unit_segment_lattice_points {p q x : Point} (h : UnitAdjacent p q)
    (hx : OnUnitSegment p q x) : x = p ∨ x = q := by
  have ht : (x.time = p.time ∧ x.depth = p.depth) ∨
      (x.time = q.time ∧ x.depth = q.depth) := by
    unfold UnitAdjacent at h
    unfold OnUnitSegment at hx
    rcases h with ⟨ht, hd⟩ | ⟨hd, ht⟩ <;>
      rcases hx with hx | hx <;> omega
  obtain ⟨ht, hd⟩ | ⟨ht, hd⟩ := ht
  · left; cases x; cases p; simp_all
  · right; cases x; cases q; simp_all

end StackSorting.GraphWidth.UCurve
