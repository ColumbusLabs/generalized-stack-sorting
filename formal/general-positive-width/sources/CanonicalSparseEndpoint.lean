import SparseEndpointTranslation

namespace StackSorting.SparseEndpointMSO
open Generalized IntervalCritical

/-- The sparse diagram is read directly from the ORIGINAL chronological event
list. Vertices are its positions; no endpoint comparison is stored as an edge.
Matching is symmetric and links opposite-color occurrences of the SAME token. -/
def eventDiagram (events : List EndpointEvent) : Model where
  domain := List.range events.length
  I x := ∃ v, events[x]? = some (.push v)
  R x := ∃ v, events[x]? = some (.pop v)
  S x y := x < events.length ∧ y < events.length ∧ x + 1 = y
  M x y := ∃ v, (events[x]? = some (.push v) ∧ events[y]? = some (.pop v)) ∨
    (events[x]? = some (.pop v) ∧ events[y]? = some (.push v))

/-- Optional list lookup and extracted position agree exactly for a unique
present event. This checks the concrete encoding, not an abstract assumption. -/
theorem event_at_iff {events : List EndpointEvent} (hn : events.Nodup)
    {event : EndpointEvent} {i : Nat} :
    events[i]? = some event ↔ event ∈ events ∧ events.idxOf event = i := by
  constructor
  · intro h
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp h
    refine ⟨he ▸ List.getElem_mem hi, ?_⟩
    rw [← he]
    exact hn.idxOf_getElem i hi
  · rintro ⟨hm, rfl⟩
    have hi := List.idxOf_lt_length_of_mem hm
    exact List.getElem?_eq_some_iff.mpr ⟨hi, List.getElem_idxOf hi⟩

theorem eventDiagram_path (events : List EndpointEvent) :
    TimePath (eventDiagram events) events.length := by
  refine ⟨rfl, ?_⟩
  intro x hx y hy
  simp only [eventDiagram, List.mem_range] at hx hy ⊢
  exact ⟨fun h => h.2.2, fun h => ⟨hx, hy, h⟩⟩

/-- Every bounded event position has exactly one color. -/
theorem eventDiagram_partition (events : List EndpointEvent) {x : Nat}
    (hx : x ∈ (eventDiagram events).domain) :
    ((eventDiagram events).I x ∨ (eventDiagram events).R x) ∧
      ¬ ((eventDiagram events).I x ∧ (eventDiagram events).R x) := by
  have hb : x < events.length := List.mem_range.mp hx
  have he : events[x]? = some events[x] := List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩
  constructor
  · cases hv : events[x] with
    | push v => exact Or.inl ⟨v, by simpa [hv] using he⟩
    | pop v => exact Or.inr ⟨v, by simpa [hv] using he⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    have := hu.symm.trans hv
    cases this

theorem eventDiagram_matching_symmetric (events : List EndpointEvent) {x y : Nat} :
    (eventDiagram events).M x y ↔ (eventDiagram events).M y x := by
  constructor <;> rintro ⟨v, h | h⟩
  · exact ⟨v, Or.inr h.symm⟩
  · exact ⟨v, Or.inl h.symm⟩
  · exact ⟨v, Or.inr h.symm⟩
  · exact ⟨v, Or.inl h.symm⟩

/-- Instantiate every encoding field from concrete list positions and matching.
Only unique events and the literal input/output token words are needed. -/
def eventEncoding {events : List EndpointEvent} {U : List Nat}
    (hn : events.Nodup) (hi : traceInputs events = U)
    (ho : (traceOutputs events).Perm U) :
    Encoding (eventDiagram events) (extractedEndpoints events) U where
  length := events.length
  path := eventDiagram_path events
  left_mem v hv := by
    have hm : EndpointEvent.push v ∈ events :=
      (mem_traceInputs v events).mp (hi.symm ▸ hv)
    exact List.mem_range.mpr (List.idxOf_lt_length_of_mem hm)
  right_mem v hv := by
    have hm := (mem_traceOutputs v events).mp (ho.mem_iff.mpr hv)
    exact List.mem_range.mpr (List.idxOf_lt_length_of_mem hm)
  left_inj u hu v hv he := by
    have hmu := (mem_traceInputs u events).mp (hi.symm ▸ hu)
    have hmv := (mem_traceInputs v events).mp (hi.symm ▸ hv)
    exact EndpointEvent.push.inj (idxOf_injective_on_events hmu hmv he)
  insert_iff x := by
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨hm, he⟩ := (event_at_iff hn).mp hv
      exact ⟨v, hi ▸ (mem_traceInputs v events).mpr hm, he⟩
    · rintro ⟨v, hv, he⟩
      exact ⟨v, (event_at_iff hn).mpr ⟨(mem_traceInputs v events).mp (hi.symm ▸ hv), he⟩⟩
  remove_right v hv := by
    exact ⟨v, (event_at_iff hn).mpr
      ⟨(mem_traceOutputs v events).mp (ho.mem_iff.mpr hv), rfl⟩⟩
  matching_iff v hv y hy := by
    have hpush : events[(extractedEndpoints events).left v]? = some (.push v) :=
      (event_at_iff hn).mpr ⟨(mem_traceInputs v events).mp (hi.symm ▸ hv), rfl⟩
    constructor
    · rintro ⟨u, ⟨hu, hu'⟩ | ⟨hu, _⟩⟩
      · have huv : u = v := EndpointEvent.push.inj (Option.some.inj (hu.symm.trans hpush))
        subst u
        exact ((event_at_iff hn).mp hu').2.symm
      · have bad := hpush.symm.trans hu
        cases bad
    · intro he
      subst y
      exact ⟨v, Or.inl ⟨hpush, (event_at_iff hn).mpr
        ⟨(mem_traceOutputs v events).mp (ho.mem_iff.mpr hv), rfl⟩⟩⟩

/-- The actual canonical permutation event diagram, independently of widths. -/
def canonicalDiagram (output : List Nat) : Model := eventDiagram (canonicalEvents 0 output)

def canonicalEncoding {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    Encoding (canonicalDiagram output)
      (extractedEndpoints (canonicalEvents 0 output)) (List.range n) := by
  obtain ⟨hn, hi, ho, _⟩ := permutation_canonical_validity hp
  exact eventEncoding hn hi (ho.symm ▸ hp)

/-- Exact translation on the actual canonical diagram, for EVERY closed formula
of the independently reviewed dense language. -/
theorem canonical_truth_preservation {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (f : EndpointMSO.Formula 0 0) :
    Satisfies (canonicalDiagram output) (translate f) ↔
      EndpointMSO.Satisfies (EndpointMSO.endpointModel
        (extractedEndpoints (canonicalEvents 0 output)) (List.range n)) f :=
  satisfies_translate (canonicalEncoding hp) f

/-- The translated sparse sentence characterizes literal generation at all
natural widths and sizes, including width zero and the empty permutation. -/
theorem generated_iff_sparseEndpointMSO {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    Generalized.Run r s [] (List.range n) output [] ↔
      Satisfies (canonicalDiagram output) (eligibilitySentence r s) :=
  (EndpointMSO.generated_iff_endpointMSO hp).trans
    (canonical_truth_preservation hp (EndpointMSO.eligibilitySentence r s)).symm

/-- Unique matching partners of insertion vertices are the original extracted
removal positions, so no alternative endpoint witness can alter a comparison. -/
theorem canonical_matching_unique {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) {v y : Nat} (hv : v ∈ List.range n)
    (hy : y ∈ (canonicalDiagram output).domain) :
    (canonicalDiagram output).M
      ((extractedEndpoints (canonicalEvents 0 output)).left v) y ↔
      y = (extractedEndpoints (canonicalEvents 0 output)).right v :=
  (canonicalEncoding hp).matching_iff v hv y hy

/-- Token labels and insertion vertices are in bijection by ORIGINAL left
endpoint positions. No chosen isomorphism or reranking is needed. -/
theorem canonical_insertion_bijection {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    (∀ v ∈ List.range n,
      (canonicalDiagram output).I ((extractedEndpoints (canonicalEvents 0 output)).left v)) ∧
    (∀ u ∈ List.range n, ∀ v ∈ List.range n,
      (extractedEndpoints (canonicalEvents 0 output)).left u =
        (extractedEndpoints (canonicalEvents 0 output)).left v → u = v) ∧
    (∀ x, (canonicalDiagram output).I x → ∃ v ∈ List.range n,
      (extractedEndpoints (canonicalEvents 0 output)).left v = x) := by
  let enc := canonicalEncoding hp
  exact ⟨fun v hv => (enc.insert_iff _).mpr ⟨v, hv, rfl⟩,
    enc.left_inj, fun x hx => (enc.insert_iff x).mp hx⟩

/-- Unique removal-side matching, derived directly from event labels. -/
theorem eventDiagram_removal_matching {events : List EndpointEvent} {U : List Nat}
    (hn : events.Nodup) (hi : traceInputs events = U)
    (ho : (traceOutputs events).Perm U) {v y : Nat} (hv : v ∈ U) :
    (eventDiagram events).M ((extractedEndpoints events).right v) y ↔
      y = (extractedEndpoints events).left v := by
  have hpop : events[(extractedEndpoints events).right v]? = some (.pop v) :=
    (event_at_iff hn).mpr ⟨(mem_traceOutputs v events).mp (ho.mem_iff.mpr hv), rfl⟩
  constructor
  · rintro ⟨u, ⟨hu, _⟩ | ⟨hu, hu'⟩⟩
    · have bad := hpop.symm.trans hu; cases bad
    · have huv := EndpointEvent.pop.inj (Option.some.inj (hu.symm.trans hpop))
      subst u
      exact ((event_at_iff hn).mp hu').2.symm
  · intro he; subst y
    exact ⟨v, Or.inr ⟨hpop, (event_at_iff hn).mpr
      ⟨(mem_traceInputs v events).mp (hi.symm ▸ hv), rfl⟩⟩⟩

/-- Every canonical vertex has precisely one partner, on BOTH colors. -/
theorem canonical_perfect_matching {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    ∀ x ∈ (canonicalDiagram output).domain,
      ∃ y ∈ (canonicalDiagram output).domain, (canonicalDiagram output).M x y ∧
        ∀ z ∈ (canonicalDiagram output).domain, (canonicalDiagram output).M x z → z = y := by
  intro x hx
  let enc := canonicalEncoding hp
  obtain ⟨hn, hi, ho, _⟩ := permutation_canonical_validity hp
  rcases (eventDiagram_partition (canonicalEvents 0 output) hx).1 with hins | hrem
  · obtain ⟨v, hv, rfl⟩ := (enc.insert_iff x).mp hins
    refine ⟨_, enc.right_mem v hv, ?_, ?_⟩
    · exact (enc.matching_iff v hv _ (enc.right_mem v hv)).mpr rfl
    · intro z hz; exact (enc.matching_iff v hv z hz).mp
  · obtain ⟨v, hv⟩ := hrem
    obtain ⟨hm, he⟩ := (event_at_iff hn).mp hv
    have hvU : v ∈ List.range n := hp.mem_iff.mp (ho ▸ (mem_traceOutputs v _).mpr hm)
    have hxv : x = (extractedEndpoints (canonicalEvents 0 output)).right v := he.symm
    subst x
    have hmatch := eventDiagram_removal_matching hn hi (ho.symm ▸ hp) (y := (extractedEndpoints (canonicalEvents 0 output)).left v) hvU
    refine ⟨_, enc.left_mem v hvU, hmatch.mpr rfl, ?_⟩
    intro z _ hz
    exact (eventDiagram_removal_matching hn hi (ho.symm ▸ hp) hvU).mp hz

/-- Matching is forward when oriented from insertion to removal. -/
theorem canonical_matching_forward {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) {x y : Nat}
    (hx : (canonicalDiagram output).I x)
    (hy : y ∈ (canonicalDiagram output).domain)
    (hm : (canonicalDiagram output).M x y) : x < y := by
  let enc := canonicalEncoding hp
  obtain ⟨v, hv, rfl⟩ := (enc.insert_iff x).mp hx
  have he := (enc.matching_iff v hv y hy).mp hm
  rw [he]
  exact (permutation_canonical_validity hp).2.2.2.1.proper v hv

/-- Positions count each event once; input plus output counts exactly those
positions. This proof uses the event list rather than endpoint assumptions. -/
theorem event_length (events : List EndpointEvent) :
    events.length = (traceInputs events).length + (traceOutputs events).length := by
  induction events with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp [traceInputs, traceOutputs, EndpointEvent.input, EndpointEvent.output] at ih ⊢ <;> omega

theorem canonical_domain_size {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) : (canonicalDiagram output).domain.length = 2 * n := by
  have hi := (permutation_canonical_validity hp).2.1
  have ho := (permutation_canonical_validity hp).2.2.1
  have hl := hp.length_eq
  simp only [List.length_range] at hl
  simp only [canonicalDiagram, eventDiagram, List.length_range]
  rw [event_length, hi, ho, List.length_range, hl]
  omega

end StackSorting.SparseEndpointMSO
