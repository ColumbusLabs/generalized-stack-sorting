import UCurveUnitGrid

namespace StackSorting.GraphWidth.UCurve

theorem Consecutive.mem_left {α} {xs : List α} {a b : α}
    (h : Consecutive xs a b) : a ∈ xs := by
  obtain ⟨pre, post, rfl⟩ := h
  simp

theorem Consecutive.mem_right {α} {xs : List α} {a b : α}
    (h : Consecutive xs a b) : b ∈ xs := by
  obtain ⟨pre, post, rfl⟩ := h
  simp

theorem Consecutive.key_le {α} (key : α → Nat) {xs : List α} {a b : α}
    (hs : xs.Pairwise (fun i j => key i ≤ key j)) (h : Consecutive xs a b) :
    key a ≤ key b := by
  obtain ⟨pre, post, rfl⟩ := h
  exact (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1 b (by simp)

theorem Consecutive.no_between {α} (key : α → Nat) {xs : List α} {a b : α}
    (hs : xs.Pairwise (fun i j => key i ≤ key j)) (h : Consecutive xs a b)
    {x : α} (hx : x ∈ xs) : ¬ (key a < key x ∧ key x < key b) := by
  obtain ⟨pre, post, rfl⟩ := h
  obtain ⟨_, ht, hc⟩ := List.pairwise_append.mp hs
  intro hb
  obtain hx | hx := List.mem_append.mp hx
  · have := hc x hx a (by simp)
    omega
  · simp only [List.mem_cons] at hx
    obtain rfl | rfl | hx := hx
    · omega
    · omega
    · have := (List.pairwise_cons.mp (List.pairwise_cons.mp ht).2).1 x hx
      omega

/-- Two consecutive open intervals in a sorted injective list cannot overlap. -/
theorem Consecutive.open_interval_unique {α} (key : α → Nat) {xs : List α}
    (hs : xs.Pairwise (fun i j => key i ≤ key j))
    (hi : ∀ a ∈ xs, ∀ b ∈ xs, key a = key b → a = b)
    {a b c d : α} (hab : Consecutive xs a b) (hcd : Consecutive xs c d)
    {position : Nat} (habp : key a < position ∧ position < key b)
    (hcdp : key c < position ∧ position < key d) : a = c ∧ b = d := by
  have hac : key a = key c := by
    have h1 := hab.no_between key hs hcd.mem_left
    have h2 := hcd.no_between key hs hab.mem_left
    omega
  have hbd : key b = key d := by
    have h1 := hab.no_between key hs hcd.mem_right
    have h2 := hcd.no_between key hs hab.mem_right
    omega
  exact ⟨hi a hab.mem_left c hcd.mem_left hac, hi b hab.mem_right d hcd.mem_right hbd⟩

theorem curve_consecutive_lt {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {i j : Node D}
    (h : Consecutive (curveNodes D v) i j) : nodePosition D v i < nodePosition D v j := by
  have hle := h.key_le (nodePosition D v) (curveNodes_sorted D v)
  have hne : nodePosition D v i ≠ nodePosition D v j := by
    intro he
    exact h.ne (curveNodes_nodup D v) (nodePosition_injective_on_curve D
      ((mem_curveNodes D v i).mp h.mem_left) ((mem_curveNodes D v j).mp h.mem_right) he)
  omega

/-- A source vertex never occurs in the open arclength interval of a source edge. -/
theorem curve_consecutive_interior_no_vertex {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {i j : Node D}
    (h : Consecutive (curveNodes D v) i j) {p : Point}
    (hp : OnCurve D v p)
    (hpi : nodePosition D v i < position D v p)
    (hpj : position D v p < nodePosition D v j) :
    ∀ q : Node D, p ≠ (nodeVertex D q).point D := by
  intro q he
  have hq : q ∈ curveNodes D v := (mem_curveNodes D v q).mpr
    ((vertex_labels_exact D (nodeVertex_valid D q) v).mpr (he ▸ hp))
  apply h.no_between (nodePosition D v) (curveNodes_sorted D v) hq
  simpa only [he, nodePosition] using And.intro hpi hpj

end StackSorting.GraphWidth.UCurve
