import ConsecutiveIntervals

namespace StackSorting.GraphWidth.UCurve

/-- A finite simple unit-grid path with specified distinct endpoints. -/
structure GridArc (p q : Point) where
  length : Nat
  positive : 0 < length
  atPoint : Nat → Point
  first : atPoint 0 = p
  last : atPoint length = q
  injective : ∀ {a b}, a ≤ length → b ≤ length → atPoint a = atPoint b → a = b
  step : ∀ a, a < length → UnitAdjacent (atPoint a) (atPoint (a+1))

def GridArc.Interior {p q : Point} (A : GridArc p q) (x : Point) : Prop :=
  ∃ a, 0 < a ∧ a < A.length ∧ A.atPoint a = x

def GridArc.OnPath {p q : Point} (A : GridArc p q) (x : Point) : Prop :=
  ∃ a, a ≤ A.length ∧ A.atPoint a = x

theorem GridArc.interior_ne_first {p q x : Point} (A : GridArc p q)
    (h : A.Interior x) : x ≠ p := by
  obtain ⟨a, ha, hb, he⟩ := h
  intro hx
  have := A.injective (Nat.le_of_lt hb) (Nat.zero_le _) (he.trans (hx.trans A.first.symm))
  omega

theorem GridArc.interior_ne_last {p q x : Point} (A : GridArc p q)
    (h : A.Interior x) : x ≠ q := by
  obtain ⟨a, ha, hb, he⟩ := h
  intro hx
  have := A.injective (Nat.le_of_lt hb) (Nat.le_refl _) (he.trans (hx.trans A.last.symm))
  omega

def GridArc.reverse {p q : Point} (A : GridArc p q) : GridArc q p where
  length := A.length
  positive := A.positive
  atPoint := fun a => A.atPoint (A.length-a)
  first := by simpa using A.last
  last := by simpa using A.first
  injective := by
    intro a b ha hb he
    have hh := A.injective (Nat.sub_le _ _) (Nat.sub_le _ _) he
    omega
  step := by
    intro a ha
    have hh := (A.step (A.length-(a+1)) (by omega)).symm
    have he : A.length-(a+1)+1 = A.length-a := by omega
    simpa only [he] using hh

theorem GridArc.interior_reverse {p q x : Point} (A : GridArc p q) :
    A.reverse.Interior x ↔ A.Interior x := by
  constructor
  · rintro ⟨a, ha, hb, he⟩
    change a < A.length at hb
    exact ⟨A.length-a, by omega, by omega, he⟩
  · rintro ⟨a, ha, hb, he⟩
    refine ⟨A.length-a, by change 0 < A.length-a; omega,
      by change A.length-a < A.length; omega, ?_⟩
    change A.atPoint (A.length-(A.length-a)) = x
    have hh : A.length-(A.length-a) = a := by omega
    simpa only [hh] using he

def GridArc.unit {p q : Point} (h : UnitAdjacent p q) : GridArc p q where
  length := 1
  positive := by decide
  atPoint := fun a => if a = 0 then p else q
  first := by simp
  last := by simp
  injective := by
    intro a b ha hb he
    have aa : a = 0 ∨ a = 1 := by omega
    have bb : b = 0 ∨ b = 1 := by omega
    rcases aa with rfl | rfl <;> rcases bb with rfl | rfl <;> simp_all [h.ne, Ne.symm h.ne]
  step := by
    intro a ha
    have he : a = 0 := by omega
    simpa [he] using h

theorem GridArc.unit_no_interior {p q x : Point} (h : UnitAdjacent p q) :
    ¬ (GridArc.unit h).Interior x := by
  rintro ⟨a, ha, hb, _⟩
  change a < 1 at hb
  omega

def sourcePoint {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (i : Node D) : Point := (nodeVertex D i).point D

theorem sourcePoint_injective {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {i j : Node D} (h : sourcePoint D i = sourcePoint D j) : i = j :=
  nodeVertex_injective D (vertex_point_injective D h)

def curveSourceArc {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {i j : Node D}
    (h : Consecutive (curveNodes D v) i j) : GridArc (sourcePoint D i) (sourcePoint D j) where
  length := nodePosition D v j - nodePosition D v i
  positive := by have := curve_consecutive_lt D h; omega
  atPoint := fun a => unitPoint D v (nodePosition D v i + a)
  first := by
    simp only [Nat.add_zero]
    exact unitPoint_position D ((vertex_labels_exact D (nodeVertex_valid D i) v).mp
      ((mem_curveNodes D v i).mp h.mem_left))
  last := by
    have hle := h.key_le (nodePosition D v) (curveNodes_sorted D v)
    have he : nodePosition D v i + (nodePosition D v j - nodePosition D v i) =
        nodePosition D v j := by omega
    rw [he]
    exact unitPoint_position D ((vertex_labels_exact D (nodeVertex_valid D j) v).mp
      ((mem_curveNodes D v j).mp h.mem_right))
  injective := by
    intro a b ha hb he
    have hj : nodePosition D v j ≤ curveLength D v := position_bound D
      ((vertex_labels_exact D (nodeVertex_valid D j) v).mp
        ((mem_curveNodes D v j).mp h.mem_right))
    have hle := h.key_le (nodePosition D v) (curveNodes_sorted D v)
    have hh := unitPoint_injective D v (by omega) (by omega) he
    omega
  step := by
    intro a ha
    have hj : nodePosition D v j ≤ curveLength D v := position_bound D
      ((vertex_labels_exact D (nodeVertex_valid D j) v).mp
        ((mem_curveNodes D v j).mp h.mem_right))
    have hle := h.key_le (nodePosition D v) (curveNodes_sorted D v)
    simpa only [Nat.add_assoc] using unitPoint_step D v (a := nodePosition D v i+a) (by omega)

theorem curveSourceArc_interior {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {i j : Node D}
    (h : Consecutive (curveNodes D v) i j) {p : Point}
    (hp : (curveSourceArc D h).Interior p) :
    OnCurve D v p ∧ nodePosition D v i < position D v p ∧
      position D v p < nodePosition D v j := by
  obtain ⟨a, ha, hb, rfl⟩ := hp
  change a < nodePosition D v j - nodePosition D v i at hb
  have hle := h.key_le (nodePosition D v) (curveNodes_sorted D v)
  have hj : nodePosition D v j ≤ curveLength D v := position_bound D
    ((vertex_labels_exact D (nodeVertex_valid D j) v).mp
      ((mem_curveNodes D v j).mp h.mem_right))
  have hbound : nodePosition D v i + a ≤ curveLength D v := by omega
  change OnCurve D v (unitPoint D v (nodePosition D v i+a)) ∧ _
  refine ⟨unitPoint_on_curve D v hbound, ?_⟩
  change nodePosition D v i < position D v (unitPoint D v (nodePosition D v i+a)) ∧
    position D v (unitPoint D v (nodePosition D v i+a)) < nodePosition D v j
  rw [position_unitPoint D v hbound]
  omega

theorem curveSourceArc_avoids_vertices {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {i j : Node D}
    (h : Consecutive (curveNodes D v) i j) {p : Point}
    (hp : (curveSourceArc D h).Interior p) (q : Node D) : p ≠ sourcePoint D q := by
  obtain ⟨hc, hi, hj⟩ := curveSourceArc_interior D h hp
  exact curve_consecutive_interior_no_vertex D h hc hi hj q

end StackSorting.GraphWidth.UCurve
