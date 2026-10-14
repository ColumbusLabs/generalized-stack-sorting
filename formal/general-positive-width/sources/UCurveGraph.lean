import UCurveOrder

namespace StackSorting.GraphWidth.UCurve

def Consecutive {α : Type} (xs : List α) (a b : α) : Prop :=
  ∃ pre post, xs = pre ++ a :: b :: post

theorem Consecutive.cons {α} {xs : List α} {a b} (h : Consecutive xs a b) (z : α) :
    Consecutive (z :: xs) a b := by
  obtain ⟨pre, post, rfl⟩ := h
  exact ⟨z :: pre, post, rfl⟩

theorem Consecutive.ne {α} {xs : List α} (hn : xs.Nodup) {a b}
    (h : Consecutive xs a b) : a ≠ b := by
  obtain ⟨pre, post, rfl⟩ := h
  have ht := (List.nodup_append.mp hn).2.1
  have ha := (List.nodup_cons.mp ht).1
  intro he
  exact ha (by simp [he])

theorem walk_from_head {α} {adj : α → α → Prop} {P : α → Prop}
    (a : α) (xs : List α) (hp : ∀ x ∈ a :: xs, P x)
    (he : ∀ x y, Consecutive (a :: xs) x y → adj x y)
    {z : α} (hz : z ∈ a :: xs) : Walk adj P a z := by
  induction xs generalizing a with
  | nil => have hez : z = a := by simpa using hz
           subst z; exact .refl (hp a (by simp))
  | cons b xs ih =>
    by_cases hza : z = a
    · subst z; exact .refl (hp a (by simp))
    · have hzt : z ∈ b :: xs := (List.mem_cons.mp hz).resolve_left hza
      exact .step (hp a (by simp)) (he a b ⟨[], xs, rfl⟩)
        (ih b (fun x hx => hp x (List.mem_cons_of_mem _ hx))
          (fun x y h => he x y (h.cons a)) hzt)

theorem walk_between_mem {α} {adj : α → α → Prop} {P : α → Prop}
    (hs : ∀ {x y}, adj x y → adj y x) (xs : List α)
    (hp : ∀ x ∈ xs, P x) (he : ∀ x y, Consecutive xs x y → adj x y)
    {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) : Walk adj P a b := by
  cases xs with
  | nil => simp at ha
  | cons z xs =>
    exact ((walk_from_head z xs hp he ha).reverse hs).trans (walk_from_head z xs hp he hb)

abbrev Node {tokens events} {E : EndpointPairing tokens events} (D : Drawing E) :=
  Fin (vertices D).length

def nodeVertex {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (i : Node D) : Vertex tokens events := (vertices D)[i.val]

theorem nodeVertex_valid {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (i : Node D) : (nodeVertex D i).Valid D :=
  (mem_vertices D _).mp (List.getElem_mem i.isLt)

theorem nodeVertex_injective {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {i j : Node D} (h : nodeVertex D i = nodeVertex D j) : i = j :=
  Fin.ext ((vertices_nodup D).getElem_inj.mp h)

def labels {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (i : Node D) : List (Fin tokens) := (nodeVertex D i).labels E

def nodePosition {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) (i : Node D) : Nat :=
  position D v ((nodeVertex D i).point D)

/-- Each token's vertices in their literal distance order along its U. -/
def curveNodes {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) : List (Node D) :=
  ((List.finRange (vertices D).length).filter (fun i => decide (v ∈ labels D i))).mergeSort
    (fun i j => decide (nodePosition D v i ≤ nodePosition D v j))

@[simp] theorem mem_curveNodes {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) (i : Node D) :
    i ∈ curveNodes D v ↔ v ∈ labels D i := by
  simp [curveNodes]

theorem curveNodes_nodup {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) : (curveNodes D v).Nodup := by
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  exact (List.nodup_finRange _).filter _

theorem curveNodes_sorted {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) :
    (curveNodes D v).Pairwise (fun i j => nodePosition D v i ≤ nodePosition D v j) := by
  have h := List.pairwise_mergeSort (le := fun i j : Node D =>
    decide (nodePosition D v i ≤ nodePosition D v j))
    (fun a b c hab hbc => by simp_all; omega)
    (fun a b => by simp; omega)
    ((List.finRange (vertices D).length).filter (fun i => decide (v ∈ labels D i)))
  simpa [curveNodes] using h

theorem nodePosition_injective_on_curve {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {i j : Node D}
    (hi : v ∈ labels D i) (hj : v ∈ labels D j)
    (he : nodePosition D v i = nodePosition D v j) : i = j := by
  apply nodeVertex_injective D
  apply vertex_point_injective D
  exact position_injective D
    ((vertex_labels_exact D (nodeVertex_valid D i) v).mp hi)
    ((vertex_labels_exact D (nodeVertex_valid D j) v).mp hj) he

def anchor {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) : Node D :=
  ⟨(vertices D).idxOf (.endpoint e), List.idxOf_lt_length_of_mem
    ((mem_vertices D (.endpoint e)).mpr trivial)⟩

@[simp] theorem nodeVertex_anchor {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) : nodeVertex D (anchor D e) = .endpoint e := by
  exact List.getElem_idxOf _

@[simp] theorem labels_anchor {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) : labels D (anchor D e) = [E.owner e] := by
  simp [labels, Vertex.labels]

theorem anchor_injective {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e f : Fin events} (h : anchor D e = anchor D f) : e = f := by
  have hh := congrArg (nodeVertex D) h
  simpa using hh

/-- The explicit subdivided U-curve graph with baseline edges. Whether this
finite graph has the needed planar embedding is a further theorem, not a field. -/
def sourceGraph {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) : Graph (vertices D).length where
  Adj i j := i ≠ j ∧ ((∃ v, Consecutive (curveNodes D v) i j ∨
    Consecutive (curveNodes D v) j i) ∨
    (∃ e f, e.val + 1 = f.val ∧
      ((i = anchor D e ∧ j = anchor D f) ∨ (j = anchor D e ∧ i = anchor D f))))
  symm := by
    intro i j ⟨hn, he⟩
    refine ⟨Ne.symm hn, ?_⟩
    obtain ⟨v, h⟩ | ⟨e, f, hef, h⟩ := he
    · exact Or.inl ⟨v, h.symm⟩
    · exact Or.inr ⟨e, f, hef, h.symm⟩
  loopless := fun _ h => h.1 rfl

theorem curve_fiber_connected {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {v : Fin tokens} {i j : Node D}
    (hi : v ∈ labels D i) (hj : v ∈ labels D j) :
    Walk (sourceGraph D).Adj (fun k => v ∈ labels D k) i j := by
  apply walk_between_mem (sourceGraph D).symm (curveNodes D v)
    (fun k hk => (mem_curveNodes D v k).mp hk) ?_
    ((mem_curveNodes D v i).mpr hi) ((mem_curveNodes D v j).mpr hj)
  intro q r hqr
  exact ⟨hqr.ne (curveNodes_nodup D v), Or.inl ⟨v, Or.inl hqr⟩⟩

theorem baseline_edge {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e f : Fin events) (h : e.val + 1 = f.val) :
    (sourceGraph D).Adj (anchor D e) (anchor D f) := by
  refine ⟨?_, Or.inr ⟨e, f, h, Or.inl ⟨rfl, rfl⟩⟩⟩
  intro he
  have hv := congrArg Fin.val (anchor_injective D he)
  omega

theorem source_labels_bound {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (i : Node D) : (labels D i).length ≤ 2 :=
  vertex_labels_bound E _

theorem source_labels_nodup {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (i : Node D) : (labels D i).Nodup :=
  vertex_labels_nodup D (nodeVertex_valid D i)

end StackSorting.GraphWidth.UCurve
