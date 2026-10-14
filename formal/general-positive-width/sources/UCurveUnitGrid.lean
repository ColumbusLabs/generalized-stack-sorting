import UCurveStemDistance

namespace StackSorting.GraphWidth.UCurve

/-- One horizontal or vertical unit segment of the nonnegative integer grid. -/
def UnitAdjacent (p q : Point) : Prop :=
  (p.time = q.time ∧ (p.depth + 1 = q.depth ∨ q.depth + 1 = p.depth)) ∨
  (p.depth = q.depth ∧ (p.time + 1 = q.time ∨ q.time + 1 = p.time))

theorem UnitAdjacent.symm {p q : Point} (h : UnitAdjacent p q) : UnitAdjacent q p := by
  unfold UnitAdjacent at *
  rcases h with ⟨ht, hd⟩ | ⟨hd, ht⟩
  · exact Or.inl ⟨ht.symm, hd.symm⟩
  · exact Or.inr ⟨hd.symm, ht.symm⟩

theorem UnitAdjacent.ne {p q : Point} (h : UnitAdjacent p q) : p ≠ q := by
  intro he
  subst q
  unfold UnitAdjacent at h
  omega

/-- Inverse arclength parametrization, including the two geometric bends. -/
def unitPoint {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) (distance : Nat) : Point :=
  if distance ≤ D.depth v then ⟨(E.left v).val, distance⟩
  else if distance ≤ D.depth v + ((E.right v).val - (E.left v).val) then
    ⟨(E.left v).val + (distance - D.depth v), D.depth v⟩
  else ⟨(E.right v).val, curveLength D v - distance⟩

theorem unitPoint_on_curve {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) {distance : Nat}
    (h : distance ≤ curveLength D v) : OnCurve D v (unitPoint D v distance) := by
  have hp := D.proper v
  unfold unitPoint
  split
  · exact Or.inl ⟨Or.inl rfl, by assumption⟩
  · split
    · right
      change (E.left v).val ≤ (E.left v).val + (distance - D.depth v) ∧
        (E.left v).val + (distance - D.depth v) ≤ (E.right v).val ∧ D.depth v = D.depth v
      exact ⟨by omega, by omega, rfl⟩
    · left
      refine ⟨Or.inr rfl, ?_⟩
      simp only [curveLength] at *
      omega

theorem position_unitPoint {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) {distance : Nat}
    (h : distance ≤ curveLength D v) : position D v (unitPoint D v distance) = distance := by
  have hp := D.proper v
  have hrne : (E.right v).val ≠ (E.left v).val := by omega
  unfold unitPoint
  split
  · simp [position]
  · rename_i hn
    split
    · rename_i hh
      have hl : (E.left v).val + (distance - D.depth v) ≠ (E.left v).val := by omega
      simp only [position, hl, ↓reduceIte]
      split <;> omega
    · simp only [position, hrne, ↓reduceIte, curveLength] at *
      omega

theorem unitPoint_position {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {p : Point} (hp : OnCurve D v p) :
    unitPoint D v (position D v p) = p := by
  have hbound : position D v p ≤ curveLength D v := position_bound D hp
  exact position_injective D (unitPoint_on_curve D v hbound) hp
    (position_unitPoint D v hbound)

theorem unitPoint_injective {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) {a b : Nat}
    (ha : a ≤ curveLength D v) (hb : b ≤ curveLength D v)
    (he : unitPoint D v a = unitPoint D v b) : a = b := by
  have hh := congrArg (position D v) he
  simpa only [position_unitPoint D v ha, position_unitPoint D v hb] using hh

theorem unitPoint_zero {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) : unitPoint D v 0 = endpointPoint (E.left v) := by
  simp [unitPoint, endpointPoint]

theorem unitPoint_end {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) :
    unitPoint D v (curveLength D v) = endpointPoint (E.right v) := by
  have h := unitPoint_position D ((endpoint_on_curve D (E.right v) v).mpr
    (E.owner_right v).symm)
  simpa only [position_right, curveLength] using h

theorem unitPoint_step {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) {a : Nat} (ha : a < curveLength D v) :
    UnitAdjacent (unitPoint D v a) (unitPoint D v (a+1)) := by
  have hp := D.proper v
  unfold curveLength at ha
  by_cases h1 : a ≤ D.depth v <;>
    by_cases h2 : a ≤ D.depth v + ((E.right v).val - (E.left v).val) <;>
    by_cases h3 : a + 1 ≤ D.depth v <;>
    by_cases h4 : a + 1 ≤ D.depth v + ((E.right v).val - (E.left v).val) <;>
    simp only [unitPoint, h1, h2, h3, h4, ↓reduceIte, UnitAdjacent, curveLength, true_and, true_or]
  all_goals omega

/-- The full U as a duplicate-free finite sequence of lattice points. -/
def unitCurve {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) : List Point :=
  (List.range (curveLength D v + 1)).map (unitPoint D v)

theorem mem_unitCurve {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) (p : Point) :
    p ∈ unitCurve D v ↔ OnCurve D v p := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact unitPoint_on_curve D v (by have := List.mem_range.mp ha; omega)
  · intro h
    exact List.mem_map.mpr ⟨position D v p,
      List.mem_range.mpr (by have := position_bound D h; unfold curveLength; omega),
      unitPoint_position D h⟩

theorem unitCurve_nodup {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) : (unitCurve D v).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.pairwise_lt_range (n := curveLength D v + 1)).imp_of_mem
  intro a b ha hb hab he
  have hae : a ≤ curveLength D v := by have := List.mem_range.mp ha; omega
  have hbe : b ≤ curveLength D v := by have := List.mem_range.mp hb; omega
  have := unitPoint_injective D v hae hbe he
  omega

end StackSorting.GraphWidth.UCurve
