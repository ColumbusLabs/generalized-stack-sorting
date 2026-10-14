import UCurveCanonical

namespace StackSorting.GraphWidth.UCurve

def curveLength {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (v : Fin tokens) : Nat :=
  2 * D.depth v + ((E.right v).val - (E.left v).val)

/-- Distance along the owner's U, now measured from the chosen endpoint. -/
def endpointDistance {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (p : Point) : Nat :=
  if e = E.left (E.owner e) then position D (E.owner e) p
  else curveLength D (E.owner e) - position D (E.owner e) p

theorem right_not_left {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e : Fin events} (he : e = E.right (E.owner e)) :
    e ≠ E.left (E.owner e) := by
  intro hl
  have hp := D.proper (E.owner e)
  have h := congrArg Fin.val (hl.symm.trans he)
  omega

theorem endpointDistance_anchor {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) : endpointDistance D e (endpointPoint e) = 0 := by
  obtain he | he := E.complete e
  · rw [endpointDistance, ite_eq_left he]
    rw [congrArg endpointPoint he, position_left]
  · rw [endpointDistance, ite_eq_right (right_not_left D he)]
    rw [congrArg endpointPoint he, position_right]
    simp [curveLength]

theorem endpointDistance_injective {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e : Fin events} {p q : Point}
    (hp : OnCurve D (E.owner e) p) (hq : OnCurve D (E.owner e) q)
    (he : endpointDistance D e p = endpointDistance D e q) : p = q := by
  apply position_injective D hp hq
  by_cases hl : e = E.left (E.owner e)
  · simpa only [endpointDistance, ite_eq_left hl] using he
  · simp only [endpointDistance, ite_eq_right hl] at he
    have hp' := position_bound D hp
    have hq' := position_bound D hq
    unfold curveLength at he
    omega

/-- Before traversing the full stem depth, a U-walk stays on that same stem. -/
theorem near_endpoint_on_stem {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e : Fin events} {p : Point}
    (hp : OnCurve D (E.owner e) p)
    (hd : endpointDistance D e p < D.depth (E.owner e)) :
    p.time = e.val ∧ p.depth = endpointDistance D e p := by
  have hc := position_cases D hp
  have hproper := D.proper (E.owner e)
  obtain he | he := E.complete e
  · have ht := congrArg Fin.val he
    simp only [endpointDistance, ite_eq_left he] at hd ⊢
    rcases hc with h | h | h <;> omega
  · have ht := congrArg Fin.val he
    simp only [endpointDistance, ite_eq_right (right_not_left D he), curveLength] at hd ⊢
    rcases hc with h | h | h <;> omega

theorem endpointDistance_crossing {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e : Fin events} {v : Fin tokens} (hc : Crosses D e v) :
    endpointDistance D e (crossingPoint D e v) = D.depth v := by
  have hproper := D.proper (E.owner e)
  have hdepth := hc.2.2
  obtain he | he := E.complete e
  · have ht : (crossingPoint D e v).time = (E.left (E.owner e)).val := congrArg Fin.val he
    rw [endpointDistance, ite_eq_left he, position, ite_eq_left ht]
    rfl
  · have ht : (crossingPoint D e v).time = (E.right (E.owner e)).val := congrArg Fin.val he
    have hn : (crossingPoint D e v).time ≠ (E.left (E.owner e)).val := by
      change e.val ≠ (E.left (E.owner e)).val
      have he' := congrArg Fin.val he
      omega
    rw [endpointDistance, ite_eq_right (right_not_left D he), position,
      ite_eq_right hn, ite_eq_left ht]
    change curveLength D (E.owner e) - (D.depth (E.owner e) +
      ((E.right (E.owner e)).val - (E.left (E.owner e)).val) +
      (D.depth (E.owner e) - D.depth v)) = D.depth v
    unfold curveLength
    omega

def nodeDistance {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (i : Node D) : Nat :=
  endpointDistance D e ((nodeVertex D i).point D)

@[simp] theorem nodeDistance_anchor {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) : nodeDistance D e (anchor D e) = 0 := by
  simpa [nodeDistance, Vertex.point] using endpointDistance_anchor D e

def directedNodes {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) : List (Node D) :=
  if e = E.left (E.owner e) then curveNodes D (E.owner e)
  else (curveNodes D (E.owner e)).reverse

@[simp] theorem mem_directedNodes {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) (i : Node D) :
    i ∈ directedNodes D e ↔ E.owner e ∈ labels D i := by
  unfold directedNodes
  split <;> simp

theorem directedNodes_nodup {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) : (directedNodes D e).Nodup := by
  unfold directedNodes
  split
  · exact curveNodes_nodup D _
  · exact List.pairwise_reverse.mpr ((curveNodes_nodup D _).imp (fun h => Ne.symm h))

theorem directedNodes_sorted {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) :
    (directedNodes D e).Pairwise (fun i j => nodeDistance D e i ≤ nodeDistance D e j) := by
  by_cases hl : e = E.left (E.owner e)
  · simpa only [directedNodes, nodeDistance, endpointDistance, ite_eq_left hl,
      nodePosition] using curveNodes_sorted D (E.owner e)
  · simp only [directedNodes, ite_eq_right hl, List.pairwise_reverse]
    apply (curveNodes_sorted D (E.owner e)).imp
    intro i j hij
    simp only [nodeDistance, endpointDistance, ite_eq_right hl]
    unfold nodePosition at hij
    omega

theorem nodeDistance_injective_on_curve {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) {e : Fin events} {i j : Node D}
    (hi : E.owner e ∈ labels D i) (hj : E.owner e ∈ labels D j)
    (he : nodeDistance D e i = nodeDistance D e j) : i = j := by
  apply nodeVertex_injective D
  apply vertex_point_injective D
  exact endpointDistance_injective D
    ((vertex_labels_exact D (nodeVertex_valid D i) _).mp hi)
    ((vertex_labels_exact D (nodeVertex_valid D j) _).mp hj) he

theorem directedNodes_starts_at_anchor {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) :
    ∃ tail, directedNodes D e = anchor D e :: tail := by
  have ha : anchor D e ∈ directedNodes D e := by simp
  have hs := directedNodes_sorted D e
  cases hx : directedNodes D e with
  | nil => simp [hx] at ha
  | cons q qs =>
    have hqmem : q ∈ directedNodes D e := by simp [hx]
    have hqle : nodeDistance D e q ≤ nodeDistance D e (anchor D e) := by
      rw [hx] at ha hs
      obtain he | he := List.mem_cons.mp ha
      · subst q; exact Nat.le_refl _
      · exact (List.pairwise_cons.mp hs).1 _ he
    have heq : q = anchor D e := by
      apply nodeDistance_injective_on_curve D ((mem_directedNodes D e q).mp hqmem)
        (by simp [labels_anchor])
      have hz := nodeDistance_anchor D e
      omega
    exact ⟨qs, by simp_all⟩

theorem Consecutive.reverse {α} {xs : List α} {a b : α}
    (h : Consecutive xs a b) : Consecutive xs.reverse b a := by
  obtain ⟨pre, post, rfl⟩ := h
  refine ⟨post.reverse, pre.reverse, ?_⟩
  simp [List.reverse_append, List.reverse_cons, List.append_assoc]

theorem directedNodes_edge {tokens events} {E : EndpointPairing tokens events}
    (D : Drawing E) (e : Fin events) {i j : Node D}
    (h : Consecutive (directedNodes D e) i j) : (sourceGraph D).Adj i j := by
  refine ⟨h.ne (directedNodes_nodup D e), Or.inl ⟨E.owner e, ?_⟩⟩
  by_cases hl : e = E.left (E.owner e)
  · exact Or.inl (by simpa only [directedNodes, ite_eq_left hl] using h)
  · right
    simpa only [directedNodes, ite_eq_right hl, List.reverse_reverse] using h.reverse

end StackSorting.GraphWidth.UCurve
