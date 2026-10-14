import SparseGraphDecomposition

namespace StackSorting.GraphWidth.UCurve

/-- Integer coordinates with nonnegative depth measured down from the baseline. -/
structure Point where
  time : Nat
  depth : Nat
  deriving DecidableEq, Repr

/-- The literal U-shaped segments for paired chronological endpoints. -/
structure Drawing {tokens events} (E : EndpointPairing tokens events) where
  depth : Fin tokens → Nat
  positive : ∀ v, 0 < depth v
  injective : ∀ {u v}, depth u = depth v → u = v
  proper : ∀ v, (E.left v).val < (E.right v).val

def endpointPoint (e : Fin events) : Point := ⟨e.val, 0⟩

def crossingPoint {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (v : Fin tokens) : Point := ⟨e.val, D.depth v⟩

/-- Closed vertical/horizontal segments, including bends and endpoints. -/
def OnCurve {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) (p : Point) : Prop :=
  (((E.left v).val = p.time ∨ (E.right v).val = p.time) ∧ p.depth ≤ D.depth v) ∨
  ((E.left v).val ≤ p.time ∧ p.time ≤ (E.right v).val ∧ p.depth = D.depth v)

/-- A transverse crossing of the stem at e with the horizontal segment of v.
Both inequalities are strict, so baseline points and bends are excluded. -/
def Crosses {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (v : Fin tokens) : Prop :=
  (E.left v).val < e.val ∧ e.val < (E.right v).val ∧ D.depth v < D.depth (E.owner e)

instance {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (v : Fin tokens) : Decidable (Crosses D e v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem endpoint_owner_eq {tokens events} (E : EndpointPairing tokens events)
    {e : Fin events} {v : Fin tokens}
    (h : (E.left v).val = e.val ∨ (E.right v).val = e.val) : E.owner e = v := by
  obtain h | h := h
  · have he : E.left v = e := Fin.ext h
    simpa [E.owner_left] using congrArg E.owner he.symm
  · have he : E.right v = e := Fin.ext h
    simpa [E.owner_right] using congrArg E.owner he.symm

theorem endpoint_on_curve {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (v : Fin tokens) :
    OnCurve D v (endpointPoint e) ↔ v = E.owner e := by
  constructor
  · rintro (⟨h, _⟩ | ⟨_, _, h⟩)
    · exact (endpoint_owner_eq E h).symm
    · have hp := D.positive v
      change 0 = D.depth v at h
      omega
  · intro h; subst v
    left
    refine ⟨?_, Nat.zero_le _⟩
    obtain he | he := E.complete e
    · exact Or.inl (congrArg Fin.val he.symm)
    · exact Or.inr (congrArg Fin.val he.symm)

theorem crossing_distinct {tokens events} {E : EndpointPairing tokens events}
    {D : Drawing E} {e v} (h : Crosses D e v) : E.owner e ≠ v := by
  intro he
  have hd := h.2.2
  rw [he] at hd
  exact Nat.lt_irrefl _ hd

/-- Exactly two token curves meet a crossing: no third curve or bend is hidden. -/
theorem crossing_on_curve {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e : Fin events} {v : Fin tokens} (h : Crosses D e v)
    (u : Fin tokens) :
    OnCurve D u (crossingPoint D e v) ↔ u = E.owner e ∨ u = v := by
  constructor
  · rintro (⟨he, _⟩ | ⟨_, _, hd⟩)
    · exact Or.inl (endpoint_owner_eq E he).symm
    · exact Or.inr (D.injective hd).symm
  · rintro (rfl | rfl)
    · left
      refine ⟨?_, Nat.le_of_lt h.2.2⟩
      obtain he | he := E.complete e
      · exact Or.inl (congrArg Fin.val he.symm)
      · exact Or.inr (congrArg Fin.val he.symm)
    · exact Or.inr ⟨Nat.le_of_lt h.1, Nat.le_of_lt h.2.1, rfl⟩

theorem crossing_point_injective {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e f : Fin events} {u v : Fin tokens}
    (h : crossingPoint D e u = crossingPoint D f v) : e = f ∧ u = v :=
  ⟨Fin.ext (congrArg Point.time h), D.injective (congrArg Point.depth h)⟩

theorem endpoint_ne_crossing {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e f : Fin events) (v : Fin tokens) :
    endpointPoint e ≠ crossingPoint D f v := by
  intro h
  have hd := congrArg Point.depth h
  have hp := D.positive v
  change 0 = D.depth v at hd
  omega

inductive Vertex (tokens events : Nat) where
  | endpoint : Fin events → Vertex tokens events
  | crossing : Fin events → Fin tokens → Vertex tokens events
  deriving DecidableEq

def Vertex.Valid {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : Vertex tokens events → Prop
  | .endpoint _ => True
  | .crossing e v => Crosses D e v

instance {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (x : Vertex tokens events) : Decidable (x.Valid D) := by
  cases x <;> simp only [Vertex.Valid] <;> infer_instance

def Vertex.point {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : Vertex tokens events → Point
  | .endpoint e => endpointPoint e
  | .crossing e v => crossingPoint D e v

def Vertex.labels {tokens events} (E : EndpointPairing tokens events) :
    Vertex tokens events → List (Fin tokens)
  | .endpoint e => [E.owner e]
  | .crossing e v => [E.owner e, v]

theorem vertex_point_injective {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {x y : Vertex tokens events} (h : x.point D = y.point D) : x = y := by
  cases x with
  | endpoint e =>
    cases y with
    | endpoint f => exact congrArg Vertex.endpoint (Fin.ext (congrArg Point.time h))
    | crossing f v => exact False.elim (endpoint_ne_crossing D e f v h)
  | crossing e u =>
    cases y with
    | endpoint f => exact False.elim (endpoint_ne_crossing D f e u h.symm)
    | crossing f v =>
      obtain ⟨rfl, rfl⟩ := crossing_point_injective D h
      rfl

theorem vertex_labels_exact {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {x : Vertex tokens events} (hx : x.Valid D) (v : Fin tokens) :
    v ∈ x.labels E ↔ OnCurve D v (x.point D) := by
  cases x with
  | endpoint e => simpa [Vertex.labels, Vertex.point] using (endpoint_on_curve D e v).symm
  | crossing e u =>
    simpa [Vertex.labels, Vertex.point] using (crossing_on_curve D hx v).symm

theorem vertex_labels_bound {tokens events} (E : EndpointPairing tokens events)
    (x : Vertex tokens events) : (x.labels E).length ≤ 2 := by
  cases x <;> simp [Vertex.labels]

theorem vertex_labels_nodup {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {x : Vertex tokens events} (hx : x.Valid D) : (x.labels E).Nodup := by
  cases x with
  | endpoint e => simp [Vertex.labels]
  | crossing e v => simp [Vertex.labels, crossing_distinct hx]

/-- Exact finite vertex set: all event endpoints and all transverse crossings.
Geometric bends remain inside edges and are deliberately not graph vertices. -/
def vertices {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : List (Vertex tokens events) := uniqueList
  ((List.finRange events).map Vertex.endpoint ++
   (List.finRange events).flatMap (fun e =>
     ((List.finRange tokens).filter (fun v => decide (Crosses D e v))).map (Vertex.crossing e)))

@[simp] theorem mem_vertices {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (x : Vertex tokens events) : x ∈ vertices D ↔ x.Valid D := by
  cases x with
  | endpoint e => simp [vertices, Vertex.Valid]
  | crossing e v => simp [vertices, Vertex.Valid]

theorem vertices_nodup {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : (vertices D).Nodup := uniqueList_nodup _

theorem vertical_owner_unique {tokens events} (E : EndpointPairing tokens events)
    {u v : Fin tokens} {x : Nat}
    (hu : (E.left u).val = x ∨ (E.right u).val = x)
    (hv : (E.left v).val = x ∨ (E.right v).val = x) : u = v := by
  obtain hu | hu := hu
  · have h := endpoint_owner_eq E (e := E.left u) (v := v)
      (hv.imp (fun h => h.trans hu.symm) (fun h => h.trans hu.symm))
    simpa [E.owner_left] using h
  · have h := endpoint_owner_eq E (e := E.right u) (v := v)
      (hv.imp (fun h => h.trans hu.symm) (fun h => h.trans hu.symm))
    simpa [E.owner_right] using h

theorem vertical_horizontal_crossing {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {u v : Fin tokens} {p : Point} (hne : u ≠ v)
    (hu : ((E.left u).val = p.time ∨ (E.right u).val = p.time) ∧ p.depth ≤ D.depth u)
    (hv : (E.left v).val ≤ p.time ∧ p.time ≤ (E.right v).val ∧ p.depth = D.depth v) :
    ∃ e, Crosses D e v ∧ E.owner e = u ∧ crossingPoint D e v = p := by
  have hs : ∃ e : Fin events, e.val = p.time ∧ E.owner e = u := by
    obtain h | h := hu.1
    · exact ⟨E.left u, h, E.owner_left u⟩
    · exact ⟨E.right u, h, E.owner_right u⟩
  obtain ⟨e, he, ho⟩ := hs
  have hlne : (E.left v).val ≠ e.val := by
    intro h
    exact hne (ho.symm.trans (endpoint_owner_eq E (Or.inl h)))
  have hrne : (E.right v).val ≠ e.val := by
    intro h
    exact hne (ho.symm.trans (endpoint_owner_eq E (Or.inr h)))
  have hdne : D.depth v ≠ D.depth u := by
    intro h
    exact hne (D.injective h).symm
  have hc : Crosses D e v := by
    unfold Crosses
    rw [ho]
    have := hu.2
    omega
  refine ⟨e, hc, ho, ?_⟩
  cases p
  simp only [crossingPoint, Point.mk.injEq]
  exact ⟨he, hv.2.2.symm⟩

/-- Every meeting of distinct token curves is one of the listed transverse
crossings. In particular no shared segment, unlisted endpoint meeting, or
unlisted crossing is omitted by the finite vertex enumeration. -/
theorem intersection_vertex {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {u v : Fin tokens} {p : Point} (hne : u ≠ v)
    (hu : OnCurve D u p) (hv : OnCurve D v p) :
    ∃ x ∈ vertices D, x.point D = p ∧ u ∈ x.labels E ∧ v ∈ x.labels E := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact False.elim (hne (vertical_owner_unique E hu.1 hv.1))
  · obtain ⟨e, hc, he, hp⟩ := vertical_horizontal_crossing D hne hu hv
    refine ⟨.crossing e v, (mem_vertices D _).mpr hc, hp, ?_, ?_⟩ <;>
      simp [Vertex.labels, he]
  · obtain ⟨e, hc, he, hp⟩ := vertical_horizontal_crossing D (Ne.symm hne) hv hu
    refine ⟨.crossing e u, (mem_vertices D _).mpr hc, hp, ?_, ?_⟩ <;>
      simp [Vertex.labels, he]
  · exact False.elim (hne (D.injective (hu.2.2.symm.trans hv.2.2)))

end StackSorting.GraphWidth.UCurve
