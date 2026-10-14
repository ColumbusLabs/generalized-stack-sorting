import EndpointDecompositionLift
import CanonicalSparseEndpoint

namespace StackSorting.GraphWidth
open FinitePort Generalized SparseEndpointMSO

/-- The loopless undirected graph of the two binary symbols S and M. The
unary event colors add no edges; the dense time order is never added. For a
TimePath of length n, Fin n names exactly its domain. -/
def sparseGraph (D : Model) (n : Nat) : Graph n where
  Adj u v := u ≠ v ∧ (D.S u.val v.val ∨ D.S v.val u.val ∨
    D.M u.val v.val ∨ D.M v.val u.val)
  symm := by
    intro u v ⟨hne, he⟩
    refine ⟨Ne.symm hne, ?_⟩
    rcases he with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  loopless := fun _ h => h.1 rfl

def eventToken : EndpointEvent → Nat
  | .push v => v
  | .pop v => v

theorem eventToken_lt {events : List EndpointEvent} {n : Nat}
    (hi : traceInputs events = List.range n)
    (ho : (traceOutputs events).Perm (List.range n))
    {e : EndpointEvent} (he : e ∈ events) : eventToken e < n := by
  cases e with
  | push v =>
    apply List.mem_range.mp
    rw [← hi]
    exact (mem_traceInputs v events).mpr he
  | pop v =>
    exact List.mem_range.mp (ho.mem_iff.mp ((mem_traceOutputs v events).mpr he))

def eventOwner {events : List EndpointEvent} {n : Nat}
    (hi : traceInputs events = List.range n)
    (ho : (traceOutputs events).Perm (List.range n)) (e : Fin events.length) : Fin n :=
  ⟨eventToken events[e.val], eventToken_lt hi ho (List.getElem_mem e.isLt)⟩

theorem eventOwner_lookup {events : List EndpointEvent} {n : Nat}
    (hi : traceInputs events = List.range n)
    (ho : (traceOutputs events).Perm (List.range n)) {i : Fin events.length} {e}
    (he : events[i.val]? = some e) : (eventOwner hi ho i).val = eventToken e := by
  have hget : events[i.val] = e :=
    Option.some.inj ((List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩).symm.trans he)
  simp [eventOwner, hget]

def eventLeft {events : List EndpointEvent} {n : Nat}
    (hi : traceInputs events = List.range n) (v : Fin n) : Fin events.length :=
  ⟨events.idxOf (.push v.val), List.idxOf_lt_length_of_mem
    ((mem_traceInputs v.val events).mp (hi ▸ List.mem_range.mpr v.isLt))⟩

def eventRight {events : List EndpointEvent} {n : Nat}
    (ho : (traceOutputs events).Perm (List.range n)) (v : Fin n) : Fin events.length :=
  ⟨events.idxOf (.pop v.val), List.idxOf_lt_length_of_mem
    ((mem_traceOutputs v.val events).mp (ho.mem_iff.mpr (List.mem_range.mpr v.isLt)))⟩

/-- Paired endpoints are extracted from the actual event list; they are not
supplied as arbitrary matching data. -/
def eventPairing {events : List EndpointEvent} {n : Nat} (hn : events.Nodup)
    (hi : traceInputs events = List.range n)
    (ho : (traceOutputs events).Perm (List.range n)) : EndpointPairing n events.length where
  left := eventLeft hi
  right := eventRight ho
  owner := eventOwner hi ho
  owner_left := by
    intro v
    apply Fin.ext
    apply eventOwner_lookup hi ho (e := .push v.val)
    exact (event_at_iff hn).mpr ⟨(mem_traceInputs v.val events).mp
      (hi ▸ List.mem_range.mpr v.isLt), rfl⟩
  owner_right := by
    intro v
    apply Fin.ext
    apply eventOwner_lookup hi ho (e := .pop v.val)
    exact (event_at_iff hn).mpr ⟨(mem_traceOutputs v.val events).mp
      (ho.mem_iff.mpr (List.mem_range.mpr v.isLt)), rfl⟩
  complete := by
    intro e
    have hiidx := hn.idxOf_getElem e.val e.isLt
    cases he : events[e.val] with
    | push v =>
      left
      apply Fin.ext
      change e.val = events.idxOf (.push (eventToken events[e.val]))
      simpa [he, eventToken] using hiidx.symm
    | pop v =>
      right
      apply Fin.ext
      change e.val = events.idxOf (.pop (eventToken events[e.val]))
      simpa [he, eventToken] using hiidx.symm

theorem matching_eventOwner {events : List EndpointEvent} {n : Nat}
    (hi : traceInputs events = List.range n)
    (ho : (traceOutputs events).Perm (List.range n)) {e f : Fin events.length}
    (hm : (eventDiagram events).M e.val f.val) : eventOwner hi ho e = eventOwner hi ho f := by
  apply Fin.ext
  obtain ⟨v, ⟨he, hf⟩ | ⟨he, hf⟩⟩ := hm
  · exact (eventOwner_lookup hi ho he).trans (eventOwner_lookup hi ho hf).symm
  · exact (eventOwner_lookup hi ho he).trans (eventOwner_lookup hi ho hf).symm

/-- Construct the cover of the EXACT S/M Gaifman graph. The assumptions are
only connected token curves, their endpoint anchors, and baseline edges in
the source graph; matching-edge coverage is derived from literal event labels. -/
def eventCurveCover {events : List EndpointEvent} {n p : Nat}
    (hn : events.Nodup) (hi : traceInputs events = List.range n)
    (ho : (traceOutputs events).Perm (List.range n)) (G : Graph p)
    (labels : Fin p → List (Fin n)) (anchor : Fin events.length → Fin p)
    (anchored : ∀ e, eventOwner hi ho e ∈ labels (anchor e))
    (fiber : ∀ {v q r}, v ∈ labels q → v ∈ labels r →
      Walk G.Adj (fun x => v ∈ labels x) q r)
    (baseline : ∀ e f, e.val + 1 = f.val → G.Adj (anchor e) (anchor f)) :
    CurveCover G (sparseGraph (eventDiagram events) events.length) (eventPairing hn hi ho) where
  labels := labels
  anchor := anchor
  anchored := anchored
  fiber := fiber
  edge := by
    intro e f hef
    rcases hef.2 with h | h | h | h
    · exact Or.inr (baseline e f h.2.2)
    · exact Or.inr (G.symm (baseline f e h.2.2))
    · exact Or.inl (matching_eventOwner hi ho h)
    · exact Or.inl (matching_eventOwner hi ho h).symm

/-- A concrete finite decomposition of the canonical sparse diagram, with
bag size 12k, follows from the listed source-curve data. The planar source
and its 3k decomposition must still be constructed to obtain the full width
theorem for all stack schedules. -/
theorem canonical_sparse_decomposition {n p t : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (G : Graph p) (T : RootedTree t)
    (D : Decomposition G T) (k : Nat) (hb : D.BagBound (3*k))
    (labels : Fin p → List (Fin n)) (hc : ∀ q, (labels q).length ≤ 2)
    (anchor : Fin (canonicalEvents 0 output).length → Fin p)
    (anchored : ∀ e, eventToken (canonicalEvents 0 output)[e.val] ∈
      (labels (anchor e)).map Fin.val)
    (fiber : ∀ {v q r}, v ∈ labels q → v ∈ labels r →
      Walk G.Adj (fun x => v ∈ labels x) q r)
    (baseline : ∀ e f, e.val + 1 = f.val → G.Adj (anchor e) (anchor f)) :
    ∃ E : Decomposition (sparseGraph (canonicalDiagram output)
      (canonicalEvents 0 output).length) T, E.BagBound (12*k) := by
  obtain ⟨hn, hi, ho, _⟩ := permutation_canonical_validity hp
  have hout : (traceOutputs (canonicalEvents 0 output)).Perm (List.range n) := ho.symm ▸ hp
  have ha : ∀ e, eventOwner hi hout e ∈ labels (anchor e) := by
    intro e
    obtain ⟨v, hv, he⟩ := List.mem_map.mp (anchored e)
    have hv' : v = eventOwner hi hout e := Fin.ext he
    exact hv' ▸ hv
  let C := eventCurveCover hn hi hout G labels anchor ha fiber baseline
  exact ⟨D.lift C.connectedLift, C.endpoint_bag_bound D k hb hc⟩

end StackSorting.GraphWidth
