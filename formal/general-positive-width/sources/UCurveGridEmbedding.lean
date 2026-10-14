import UCurveGridDisjoint

namespace StackSorting.GraphWidth.UCurve

theorem baseline_unit {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e f : Fin events} (h : e.val + 1 = f.val) :
    UnitAdjacent (sourcePoint D (anchor D e)) (sourcePoint D (anchor D f)) := by
  simp only [sourcePoint, nodeVertex_anchor, Vertex.point, endpointPoint, UnitAdjacent]
  exact Or.inr ⟨trivial, Or.inl h⟩

/-- A source edge's chosen geometric representative. Reversed U-arcs and
reversed baseline edges have explicit orientations. -/
inductive EdgeRoute {tokens events} {E : EndpointPairing tokens events} (D : Drawing E) :
    Node D → Node D → Type
  | forward {v i j} : Consecutive (curveNodes D v) i j → EdgeRoute D i j
  | backward {v i j} : Consecutive (curveNodes D v) j i → EdgeRoute D i j
  | baseline {e f} : e.val + 1 = f.val → EdgeRoute D (anchor D e) (anchor D f)
  | baselineBack {e f} : e.val + 1 = f.val → EdgeRoute D (anchor D f) (anchor D e)

def EdgeRoute.arc {tokens events} {E : EndpointPairing tokens events} {D : Drawing E}
    {i j : Node D} : EdgeRoute D i j → GridArc (sourcePoint D i) (sourcePoint D j)
  | .forward h => curveSourceArc D h
  | .backward h => (curveSourceArc D h).reverse
  | .baseline h => GridArc.unit (baseline_unit D h)
  | .baselineBack h => GridArc.unit (baseline_unit D h).symm

theorem source_edge_route {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {i j : Node D} (h : (sourceGraph D).Adj i j) : Nonempty (EdgeRoute D i j) := by
  obtain ⟨_, h⟩ := h
  obtain ⟨v, hv | hv⟩ | ⟨e, f, hef, ⟨hi, hj⟩ | ⟨hj, hi⟩⟩ := h
  · exact ⟨.forward hv⟩
  · exact ⟨.backward hv⟩
  · subst i; subst j; exact ⟨.baseline hef⟩
  · subst i; subst j; exact ⟨.baselineBack hef⟩

theorem EdgeRoute.avoids_vertices {tokens events} {E : EndpointPairing tokens events}
    {D : Drawing E} {i j : Node D} (R : EdgeRoute D i j) {p : Point}
    (hp : R.arc.Interior p) (q : Node D) : p ≠ sourcePoint D q := by
  cases R with
  | forward h => exact curveSourceArc_avoids_vertices D h hp q
  | backward h =>
    exact curveSourceArc_avoids_vertices D h ((curveSourceArc D h).interior_reverse.mp hp) q
  | baseline h => exact False.elim (GridArc.unit_no_interior (baseline_unit D h) hp)
  | baselineBack h => exact False.elim (GridArc.unit_no_interior (baseline_unit D h).symm hp)

theorem EdgeRoute.positive_interior {tokens events} {E : EndpointPairing tokens events}
    {D : Drawing E} {i j : Node D} (R : EdgeRoute D i j) {p : Point}
    (hp : R.arc.Interior p) : 0 < p.depth := by
  cases R with
  | forward h => exact curveSourceArc_positive_interior D h hp
  | backward h =>
    exact curveSourceArc_positive_interior D h ((curveSourceArc D h).interior_reverse.mp hp)
  | baseline h => exact False.elim (GridArc.unit_no_interior (baseline_unit D h) hp)
  | baselineBack h => exact False.elim (GridArc.unit_no_interior (baseline_unit D h).symm hp)

theorem EdgeRoute.interiors_same_edge {tokens events} {E : EndpointPairing tokens events}
    {D : Drawing E} {i j k l : Node D} (R : EdgeRoute D i j) (S : EdgeRoute D k l)
    {p : Point} (hp : R.arc.Interior p) (hq : S.arc.Interior p) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  cases R with
  | baseline h => exact False.elim (GridArc.unit_no_interior (baseline_unit D h) hp)
  | baselineBack h => exact False.elim (GridArc.unit_no_interior (baseline_unit D h).symm hp)
  | forward h =>
    cases S with
    | baseline g => exact False.elim (GridArc.unit_no_interior (baseline_unit D g) hq)
    | baselineBack g => exact False.elim (GridArc.unit_no_interior (baseline_unit D g).symm hq)
    | forward g => exact Or.inl (curveSourceArc_interiors_unique D h g hp hq)
    | backward g => exact Or.inr (curveSourceArc_interiors_unique D h g hp
        ((curveSourceArc D g).interior_reverse.mp hq))
  | backward h =>
    have hp' := (curveSourceArc D h).interior_reverse.mp hp
    cases S with
    | baseline g => exact False.elim (GridArc.unit_no_interior (baseline_unit D g) hq)
    | baselineBack g => exact False.elim (GridArc.unit_no_interior (baseline_unit D g).symm hq)
    | forward g =>
      have he := curveSourceArc_interiors_unique D h g hp' hq
      exact Or.inr ⟨he.2, he.1⟩
    | backward g =>
      have he := curveSourceArc_interiors_unique D h g hp'
        ((curveSourceArc D g).interior_reverse.mp hq)
      exact Or.inl ⟨he.2, he.1⟩

/-- Each unoriented simple edge is represented exactly once by its index order. -/
structure OrderedEdge {n : Nat} (G : Graph n) where
  low : Fin n
  high : Fin n
  ordered : low.val < high.val
  adjacent : G.Adj low high

theorem OrderedEdge.ext {n} {G : Graph n} {e f : OrderedEdge G}
    (hl : e.low = f.low) (hh : e.high = f.high) : e = f := by
  cases e; cases f; simp_all

/-- A finite unit-grid subdivision certificate. Plane-map faces and Euler
properties are further constructions, not fields hidden in this definition. -/
structure GridSubdivision {n : Nat} (G : Graph n) where
  point : Fin n → Point
  injective : ∀ {i j}, point i = point j → i = j
  route : (e : OrderedEdge G) → GridArc (point e.low) (point e.high)
  avoids_vertices : ∀ e p, (route e).Interior p → ∀ v, p ≠ point v
  disjoint : ∀ e f p, (route e).Interior p → (route f).Interior p → e = f

noncomputable def chosenEdgeRoute {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : OrderedEdge (sourceGraph D)) : EdgeRoute D e.low e.high :=
  Classical.choice (source_edge_route D e.adjacent)

/-- The explicit source graph has a constructed grid subdivision certificate. -/
noncomputable def sourceGridSubdivision {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : GridSubdivision (sourceGraph D) where
  point := sourcePoint D
  injective := sourcePoint_injective D
  route := fun e => (chosenEdgeRoute D e).arc
  avoids_vertices := fun e p hp v => (chosenEdgeRoute D e).avoids_vertices hp v
  disjoint := by
    intro e f p hp hq
    obtain ⟨hl, hh⟩ | ⟨hl, hh⟩ := (chosenEdgeRoute D e).interiors_same_edge
      (chosenEdgeRoute D f) hp hq
    · exact OrderedEdge.ext hl hh
    · have he := e.ordered
      have hf := f.ordered
      have h1 := congrArg Fin.val hl
      have h2 := congrArg Fin.val hh
      omega

theorem sourceGridSubdivision_positive_interior {tokens events}
    {E : EndpointPairing tokens events} (D : Drawing E)
    (e : OrderedEdge (sourceGraph D)) {p : Point}
    (hp : ((sourceGridSubdivision D).route e).Interior p) : 0 < p.depth :=
  (chosenEdgeRoute D e).positive_interior hp

end StackSorting.GraphWidth.UCurve
