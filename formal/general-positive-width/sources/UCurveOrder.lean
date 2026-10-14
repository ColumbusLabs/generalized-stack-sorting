import UCurveGeometry

namespace StackSorting.GraphWidth.UCurve

/-- Distance along the U, from its insertion endpoint down, across, then up.
Bends need no separate vertices. -/
def position {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) (p : Point) : Nat :=
  if p.time = (E.left v).val then p.depth
  else if p.time = (E.right v).val then
    D.depth v + ((E.right v).val - (E.left v).val) + (D.depth v - p.depth)
  else D.depth v + (p.time - (E.left v).val)

theorem position_cases {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {p : Point} (hp : OnCurve D v p) :
    (p.time = (E.left v).val ∧ p.depth ≤ D.depth v ∧ position D v p = p.depth) ∨
    (p.time = (E.right v).val ∧ p.depth ≤ D.depth v ∧
      position D v p = D.depth v + ((E.right v).val - (E.left v).val) +
        (D.depth v - p.depth)) ∨
    ((E.left v).val < p.time ∧ p.time < (E.right v).val ∧ p.depth = D.depth v ∧
      position D v p = D.depth v + (p.time - (E.left v).val)) := by
  have hproper := D.proper v
  by_cases hl : p.time = (E.left v).val
  · left
    refine ⟨hl, ?_, by simp [position, hl]⟩
    rcases hp with h | h <;> omega
  · right
    by_cases hr : p.time = (E.right v).val
    · left
      refine ⟨hr, ?_, by simp only [position, ite_eq_right hl, ite_eq_left hr]⟩
      rcases hp with h | h <;> omega
    · right
      rcases hp with h | h
      · omega
      · exact ⟨by omega, by omega, h.2.2, by simp only [position, ite_eq_right hl, ite_eq_right hr]⟩

theorem position_injective {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {p q : Point}
    (hp : OnCurve D v p) (hq : OnCurve D v q)
    (he : position D v p = position D v q) : p = q := by
  have hproper := D.proper v
  have hc := position_cases D hp
  have hd := position_cases D hq
  have ht : p.time = q.time ∧ p.depth = q.depth := by
    rcases hc with h | h | h <;> rcases hd with j | j | j <;> omega
  cases p; cases q
  simp_all

theorem position_left {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) : position D v (endpointPoint (E.left v)) = 0 := by
  simp [position, endpointPoint]

theorem position_right {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) : position D v (endpointPoint (E.right v)) =
      2 * D.depth v + ((E.right v).val - (E.left v).val) := by
  have hp := D.proper v
  have he : (E.right v).val ≠ (E.left v).val := by omega
  simp [position, endpointPoint, he]
  omega

theorem position_bound {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {p : Point} (hp : OnCurve D v p) :
    position D v p ≤ 2 * D.depth v + ((E.right v).val - (E.left v).val) := by
  have hproper := D.proper v
  rcases position_cases D hp with h | h | h <;> omega

end StackSorting.GraphWidth.UCurve
