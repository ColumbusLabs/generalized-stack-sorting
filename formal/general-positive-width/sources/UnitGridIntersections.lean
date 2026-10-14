import UCurveGridEmbedding

namespace StackSorting.GraphWidth.UCurve

/-- The bounding rectangles of two closed axis-aligned segments overlap.
For unit grid segments this excludes crossings without a common endpoint. -/
def SegmentBoxesMeet (p q r s : Point) : Prop :=
  min p.time q.time ≤ max r.time s.time ∧
  min r.time s.time ≤ max p.time q.time ∧
  min p.depth q.depth ≤ max r.depth s.depth ∧
  min r.depth s.depth ≤ max p.depth q.depth

theorem unit_interval_contains {a b x : Nat} (h : a + 1 = b ∨ b + 1 = a)
    (hl : min a b ≤ x) (hu : x ≤ max a b) : x = a ∨ x = b := by
  rcases h with h | h <;> omega

theorem unit_intervals_overlap {a b c d : Nat}
    (h : a + 1 = b ∨ b + 1 = a) (g : c + 1 = d ∨ d + 1 = c)
    (hl : min a b ≤ max c d) (hu : min c d ≤ max a b) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  rcases h with h | h <;> rcases g with g | g <;> omega

/-- Closed unit grid segments cannot cross except at a common endpoint.
The statement also includes coincident segments. It is stronger than a
classification restricted to their integer-coordinate points. -/
theorem unit_segments_meet_endpoints {p q r s : Point}
    (hpq : UnitAdjacent p q) (hrs : UnitAdjacent r s)
    (hm : SegmentBoxesMeet p q r s) :
    p = r ∨ p = s ∨ q = r ∨ q = s := by
  have he :
      (p.time = r.time ∧ p.depth = r.depth) ∨
      (p.time = s.time ∧ p.depth = s.depth) ∨
      (q.time = r.time ∧ q.depth = r.depth) ∨
      (q.time = s.time ∧ q.depth = s.depth) := by
    unfold UnitAdjacent at hpq hrs
    rcases hpq with ⟨ht, hd⟩ | ⟨hd, ht⟩
    · rcases hrs with ⟨ht', hd'⟩ | ⟨hd', ht'⟩
      · have hx : p.time = r.time := by
          have h := hm; simp only [SegmentBoxesMeet, ← ht, ← ht', Nat.min_self, Nat.max_self] at h
          omega
        have hy := unit_intervals_overlap hd hd' hm.2.2.1 hm.2.2.2
        clear hm
        omega
      · have h := hm
        simp only [SegmentBoxesMeet, ← ht, ← hd', Nat.min_self, Nat.max_self] at h
        have hx := unit_interval_contains ht' h.2.1 h.1
        have hy := unit_interval_contains hd h.2.2.1 h.2.2.2
        clear h hm
        omega
    · rcases hrs with ⟨ht', hd'⟩ | ⟨hd', ht'⟩
      · have h := hm
        simp only [SegmentBoxesMeet, ← hd, ← ht', Nat.min_self, Nat.max_self] at h
        have hx := unit_interval_contains ht h.1 h.2.1
        have hy := unit_interval_contains hd' h.2.2.2 h.2.2.1
        clear h hm
        omega
      · have hy : p.depth = r.depth := by
          have h := hm; simp only [SegmentBoxesMeet, ← hd, ← hd', Nat.min_self, Nat.max_self] at h
          omega
        have hx := unit_intervals_overlap ht ht' hm.1 hm.2.1
        clear hm
        omega
  rcases he with h | h | h | h
  · left; cases p; cases r; simp_all
  · right; left; cases p; cases s; simp_all
  · right; right; left; cases q; cases r; simp_all
  · right; right; right; cases q; cases s; simp_all

/-- An abstract ordered coordinate realization. Strict monotonicity rules
out any overlap of integer intervals that are disjoint on the grid. -/
structure OrderedCoordinates (α : Type) [LE α] [LT α] where
  coord : Nat → α
  strict : ∀ {a b}, a < b → coord a < coord b
  conflict : ∀ {x y : α}, x < y → y ≤ x → False
  trans : ∀ {x y z : α}, x ≤ y → y ≤ z → x ≤ z

/-- Coordinate-wise membership in a closed segment's bounding rectangle. -/
def InCoordinateBox {α : Type} [LE α] [LT α] (C : OrderedCoordinates α)
    (p q : Point) (x y : α) : Prop :=
  C.coord (min p.time q.time) ≤ x ∧ x ≤ C.coord (max p.time q.time) ∧
  C.coord (min p.depth q.depth) ≤ y ∧ y ≤ C.coord (max p.depth q.depth)

theorem coordinate_boxes_meet {α : Type} [LE α] [LT α]
    (C : OrderedCoordinates α) {p q r s : Point} {x y : α}
    (hpq : InCoordinateBox C p q x y) (hrs : InCoordinateBox C r s x y) :
    SegmentBoxesMeet p q r s := by
  obtain ⟨ha, hb, hc, hd⟩ := hpq
  obtain ⟨he, hf, hg, hh⟩ := hrs
  have h1 := C.trans ha hf
  have h2 := C.trans he hb
  have h3 := C.trans hc hh
  have h4 := C.trans hg hd
  have a : min p.time q.time ≤ max r.time s.time := by
    apply Nat.le_of_not_gt
    intro h
    exact C.conflict (C.strict h) h1
  have b : min r.time s.time ≤ max p.time q.time := by
    apply Nat.le_of_not_gt
    intro h
    exact C.conflict (C.strict h) h2
  have c : min p.depth q.depth ≤ max r.depth s.depth := by
    apply Nat.le_of_not_gt
    intro h
    exact C.conflict (C.strict h) h3
  have d : min r.depth s.depth ≤ max p.depth q.depth := by
    apply Nat.le_of_not_gt
    intro h
    exact C.conflict (C.strict h) h4
  exact ⟨a,b,c,d⟩

/-- In every strictly ordered coordinate realization, unit segments whose
closed boxes meet must have a common lattice endpoint. No density or
completeness assumption on the coordinate type is needed. -/
theorem realized_unit_segments_meet_endpoints {α : Type} [LE α] [LT α]
    (C : OrderedCoordinates α) {p q r s : Point} {x y : α}
    (hpq : UnitAdjacent p q) (hrs : UnitAdjacent r s)
    (hx : InCoordinateBox C p q x y) (hy : InCoordinateBox C r s x y) :
    p = r ∨ p = s ∨ q = r ∨ q = s :=
  unit_segments_meet_endpoints hpq hrs (coordinate_boxes_meet C hx hy)

end StackSorting.GraphWidth.UCurve
