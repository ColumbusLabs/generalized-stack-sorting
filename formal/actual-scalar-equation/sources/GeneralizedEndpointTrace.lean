import GeneralizedGlobalOrder
import IntervalEndpointHistory

/-! Endpoint extraction metadata for the exact existing executable history.
No input/output inversion or relabelling is performed. -/
namespace StackSorting.Generalized
open List

inductive EndpointEvent where
  | push (token : Nat)
  | pop (token : Nat)
  deriving DecidableEq, Repr

def EndpointEvent.input : EndpointEvent → List Nat
  | .push v => [v]
  | .pop _ => []

def EndpointEvent.output : EndpointEvent → List Nat
  | .push _ => []
  | .pop v => [v]

def traceInputs (events : List EndpointEvent) : List Nat := events.flatMap EndpointEvent.input

def traceOutputs (events : List EndpointEvent) : List Nat := events.flatMap EndpointEvent.output

/-- This is annotation of the existing raw step equations, not a new transition
semantics. Each raw operation gets exactly one event with its actual labels. -/
inductive ExactTrace (r s : Nat) :
    List RawOp → List Nat → List EndpointEvent → List Nat → List Nat → Prop where
  | nil (held : List Nat) : ExactTrace r s [] held [] held []
  | cons {op : RawOp} {ops : List RawOp} {held middle final output : List Nat}
      {event : EndpointEvent} {events : List EndpointEvent}
      (step_eq : step r s op held = some (middle, event.output))
      (input_eq : introduced op = event.input)
      (tail : ExactTrace r s ops middle events final output) :
      ExactTrace r s (op :: ops) held (event :: events) final (event.output ++ output)

theorem Step.event_shape {r s : Nat} {held input output after : List Nat}
    (h : Step r s held input output after) :
    ∃ event : EndpointEvent, input = event.input ∧ output = event.output := by
  cases h with
  | push pre post v _ => exact ⟨.push v, rfl, rfl⟩
  | pop pre post v _ => exact ⟨.pop v, rfl, rfl⟩

/-- Extract labels from the actual successful step results of the original ops. -/
theorem run_exact_trace {r s : Nat} {ops : List RawOp} {held final output : List Nat}
    (h : Generalized.run r s ops held = some (final, output)) :
    ∃ events, ExactTrace r s ops held events final output := by
  induction ops generalizing held final output with
  | nil =>
    simp [Generalized.run] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨[], .nil held⟩
  | cons op ops ih =>
    obtain ⟨middle, emitted, rest, hs, ht, ho⟩ := split_run r s op ops held final output h
    obtain ⟨event, hi, he⟩ := (step_relational r s op held middle emitted hs).event_shape
    obtain ⟨events, htr⟩ := ih ht
    refine ⟨event :: events, ?_⟩
    rw [← ho, he]
    exact .cons (by simpa [he] using hs) hi htr

theorem ExactTrace.run {r s : Nat} {ops : List RawOp} {held final output : List Nat}
    {events : List EndpointEvent} (h : ExactTrace r s ops held events final output) :
    Generalized.run r s ops held = some (final, output) := by
  induction h with
  | nil => rfl
  | cons hs hi _ ih => simp [Generalized.run, hs, ih]

theorem ExactTrace.length {r s : Nat} {ops : List RawOp} {held final output : List Nat}
    {events : List EndpointEvent} (h : ExactTrace r s ops held events final output) :
    events.length = ops.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simpa using congrArg Nat.succ ih

theorem ExactTrace.inputs {r s : Nat} {ops : List RawOp} {held final output : List Nat}
    {events : List EndpointEvent} (h : ExactTrace r s ops held events final output) :
    traceInputs events = Generalized.inputs ops := by
  induction h with
  | nil => rfl
  | cons _ hi _ ih => simp only [traceInputs, Generalized.inputs, List.flatMap_cons] at ih ⊢; rw [hi, ih]

theorem ExactTrace.outputs {r s : Nat} {ops : List RawOp} {held final output : List Nat}
    {events : List EndpointEvent} (h : ExactTrace r s ops held events final output) :
    traceOutputs events = output := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp only [traceOutputs, List.flatMap_cons] at ih ⊢; rw [ih]

theorem ExactTrace.supply {r s : Nat} {ops : List RawOp} {held final output : List Nat}
    {events : List EndpointEvent} (h : ExactTrace r s ops held events final output) :
    (held ++ traceInputs events).Perm (traceOutputs events ++ final) := by
  rw [h.inputs, h.outputs]
  exact (run_relational r s ops held final output h.run).supply

/-- Taking any number of events gives the same raw prefix and its actual result. -/
theorem ExactTrace.take {r s : Nat} {ops : List RawOp} {held final output : List Nat}
    {events : List EndpointEvent} (h : ExactTrace r s ops held events final output) (m : Nat) :
    ∃ middle emitted, ExactTrace r s (ops.take m) held (events.take m) middle emitted := by
  induction h generalizing m with
  | nil => exact ⟨_, [], by simpa using ExactTrace.nil _⟩
  | cons hs hi _ ih =>
    cases m with
    | zero => exact ⟨_, [], .nil _⟩
    | succ m =>
      obtain ⟨middle, emitted, ht⟩ := ih m
      exact ⟨middle, _ ++ emitted, by simpa using ExactTrace.cons hs hi ht⟩

theorem mem_traceInputs (v : Nat) (events : List EndpointEvent) :
    v ∈ traceInputs events ↔ EndpointEvent.push v ∈ events := by
  induction events with
  | nil => simp [traceInputs]
  | cons event events ih =>
    change (v ∈ event.input ++ traceInputs events) ↔ EndpointEvent.push v ∈ event :: events
    cases event <;> simp [EndpointEvent.input, ih]

theorem mem_traceOutputs (v : Nat) (events : List EndpointEvent) :
    v ∈ traceOutputs events ↔ EndpointEvent.pop v ∈ events := by
  induction events with
  | nil => simp [traceOutputs]
  | cons event events ih =>
    change (v ∈ event.output ++ traceOutputs events) ↔ EndpointEvent.pop v ∈ event :: events
    cases event <;> simp [EndpointEvent.output, ih]

theorem trace_nodup {events : List EndpointEvent}
    (hi : (traceInputs events).Nodup) (ho : (traceOutputs events).Nodup) : events.Nodup := by
  induction events with
  | nil => exact .nil
  | cons event events ih =>
    cases event with
    | push v =>
      simp only [traceInputs, List.flatMap_cons, EndpointEvent.input, List.singleton_append,
        List.nodup_cons] at hi
      have ho' : (traceOutputs events).Nodup := by simpa [traceOutputs, EndpointEvent.output] using ho
      exact List.nodup_cons.mpr ⟨fun h => hi.1 ((mem_traceInputs v events).mpr h), ih hi.2 ho'⟩
    | pop v =>
      simp only [traceOutputs, List.flatMap_cons, EndpointEvent.output, List.singleton_append,
        List.nodup_cons] at ho
      have hi' : (traceInputs events).Nodup := by simpa [traceInputs, EndpointEvent.input] using hi
      exact List.nodup_cons.mpr ⟨fun h => ho.1 ((mem_traceOutputs v events).mpr h), ih hi' ho.2⟩

/-- A present event has occurred in a prefix iff its unique first position is
strictly before that prefix's operation count. -/
theorem mem_take_iff_idxOf_lt {event : EndpointEvent} {events : List EndpointEvent}
    (hm : event ∈ events) (m : Nat) :
    event ∈ events.take m ↔ events.idxOf event < m := by
  induction m generalizing events with
  | zero => simp
  | succ m ih =>
    cases events with
    | nil => simp at hm
    | cons head rest =>
      by_cases heq : head = event
      · subst head; simp
      · have htail : event ∈ rest := by simpa [List.mem_cons, Ne.symm heq] using hm
        simpa [List.take_succ_cons, List.idxOf_cons, heq, Ne.symm heq] using ih htail

/-- Index positions of present events determine their exact event labels. -/
theorem idxOf_injective_on_events {a b : EndpointEvent} {events : List EndpointEvent}
    (ha : a ∈ events) (hb : b ∈ events) (heq : events.idxOf a = events.idxOf b) : a = b := by
  have hia := List.idxOf_lt_length_of_mem ha
  have hib := List.idxOf_lt_length_of_mem hb
  calc
    a = events[events.idxOf a] := (List.getElem_idxOf hia).symm
    _ = events[events.idxOf b] := by congr 1
    _ = b := List.getElem_idxOf hib

/-- Natural event indices, with no standardization or inversion of labels. -/
def extractedEndpoints (events : List EndpointEvent) : IntervalCritical.Endpoints where
  left v := events.idxOf (.push v)
  right v := events.idxOf (.pop v)

/-- Every supplied token has its unique insertion and removal event in a complete
empty-to-empty history. The words retain the original input/output orientation. -/
theorem ExactTrace.complete_event_members {r s v : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output : List Nat}
    (h : ExactTrace r s ops [] events [] output) (hv : v ∈ Generalized.inputs ops) :
    EndpointEvent.push v ∈ events ∧ EndpointEvent.pop v ∈ events := by
  have hi : v ∈ traceInputs events := by simpa [h.inputs] using hv
  have hp : (traceInputs events).Perm (traceOutputs events) := by simpa using h.supply
  exact ⟨(mem_traceInputs v events).mp hi, (mem_traceOutputs v events).mp (hp.mem_iff.mp hi)⟩

theorem ExactTrace.complete_nodup {r s : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output : List Nat}
    (h : ExactTrace r s ops [] events [] output) (hn : (Generalized.inputs ops).Nodup) : events.Nodup := by
  have hi : (traceInputs events).Nodup := by simpa [h.inputs] using hn
  have hp : (traceInputs events).Perm (traceOutputs events) := by simpa using h.supply
  exact trace_nodup hi (hp.nodup_iff.mp hi)

/-- Every extracted event time is a true index of the original raw sequence. -/
theorem ExactTrace.endpoint_bounds {r s v : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output : List Nat}
    (h : ExactTrace r s ops [] events [] output) (hv : v ∈ Generalized.inputs ops) :
    (extractedEndpoints events).left v < ops.length ∧
      (extractedEndpoints events).right v < ops.length := by
  obtain ⟨hi, ho⟩ := h.complete_event_members hv
  simpa [extractedEndpoints, h.length] using
    And.intro (List.idxOf_lt_length_of_mem hi) (List.idxOf_lt_length_of_mem ho)

/-- The raw-history conservation law forces every push before its matching pop;
unique present event indices give all endpoint distinctness conditions. -/
theorem ExactTrace.endpoint_wellFormed {r s : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output : List Nat}
    (h : ExactTrace r s ops [] events [] output) (hn : (Generalized.inputs ops).Nodup) :
    IntervalCritical.WellFormed (extractedEndpoints events) (Generalized.inputs ops) := by
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨hi, ho⟩ := h.complete_event_members hv
    let b := events.idxOf (.pop v)
    have hpop : EndpointEvent.pop v ∈ events.take (b+1) :=
      (mem_take_iff_idxOf_lt ho (b+1)).mpr (Nat.lt_succ_self b)
    obtain ⟨middle, emitted, ht⟩ := h.take (b+1)
    have hp : (traceInputs (events.take (b+1))).Perm (traceOutputs (events.take (b+1)) ++ middle) := by
      simpa using ht.supply
    have hout : v ∈ traceOutputs (events.take (b+1)) := (mem_traceOutputs v _).mpr hpop
    have hin : v ∈ traceInputs (events.take (b+1)) := hp.mem_iff.mpr (by simp [hout])
    have hpush := (mem_traceInputs v _).mp hin
    have hle := (mem_take_iff_idxOf_lt hi (b+1)).mp hpush
    have hne : events.idxOf (.push v) ≠ events.idxOf (.pop v) := by
      intro heq
      have bad := idxOf_injective_on_events hi ho heq
      cases bad
    change events.idxOf (.push v) < events.idxOf (.pop v)
    dsimp [b] at hle
    omega
  · intro u hu v hv heq
    have hiu := (h.complete_event_members hu).1
    have hiv := (h.complete_event_members hv).1
    have he := idxOf_injective_on_events hiu hiv heq
    exact EndpointEvent.push.inj he
  · intro u hu v hv heq
    have hiu := (h.complete_event_members hu).2
    have hiv := (h.complete_event_members hv).2
    have he := idxOf_injective_on_events hiu hiv heq
    exact EndpointEvent.pop.inj he
  · intro u hu v hv heq
    have hiu := (h.complete_event_members hu).1
    have hov := (h.complete_event_members hv).2
    have he := idxOf_injective_on_events hiu hov heq
    cases he

/-- A given successful raw prefix has exactly the taken event annotation. -/
theorem ExactTrace.take_of_run {r s m : Nat} {ops : List RawOp}
    {held final output middle emitted : List Nat} {events : List EndpointEvent}
    (h : ExactTrace r s ops held events final output)
    (hp : Generalized.run r s (ops.take m) held = some (middle, emitted)) :
    ExactTrace r s (ops.take m) held (events.take m) middle emitted := by
  obtain ⟨middle', emitted', ht⟩ := h.take m
  have heq : middle' = middle ∧ emitted' = emitted := by
    simpa only [Option.some.injEq, Prod.mk.injEq] using ht.run.symm.trans hp
  rcases heq with ⟨rfl, rfl⟩
  exact ht

/-- No token outside the original input supply occurs in an actual prefix stack. -/
theorem ExactTrace.prefix_held_mem_input {r s m v : Nat} {ops : List RawOp}
    {output middle emitted : List Nat} {events : List EndpointEvent}
    (h : ExactTrace r s ops [] events [] output)
    (hp : Generalized.run r s (ops.take m) [] = some (middle, emitted)) (hv : v ∈ middle) :
    v ∈ Generalized.inputs ops := by
  have ht := h.take_of_run hp
  have hs : (traceInputs (events.take m)).Perm (traceOutputs (events.take m) ++ middle) := by
    simpa using ht.supply
  have hi : v ∈ traceInputs (events.take m) := hs.mem_iff.mpr (by simp [hv])
  have hpush := (mem_traceInputs v _).mp hi
  have hin := (mem_traceInputs v events).mpr (List.mem_of_mem_take hpush)
  simpa [h.inputs] using hin

/-- The precise active-interval invariant at every actual raw prefix, for each
supplied token. `m` is the number of already executed raw operations. -/
theorem ExactTrace.prefix_active {r s m v : Nat} {ops : List RawOp}
    {output middle emitted : List Nat} {events : List EndpointEvent}
    (h : ExactTrace r s ops [] events [] output) (hn : (Generalized.inputs ops).Nodup)
    (hp : Generalized.run r s (ops.take m) [] = some (middle, emitted)) (hv : v ∈ Generalized.inputs ops) :
    v ∈ middle ↔ (extractedEndpoints events).left v < m ∧ m ≤ (extractedEndpoints events).right v := by
  have ht := h.take_of_run hp
  have he : Generalized.inputs (ops.take m) ++ Generalized.inputs (ops.drop m) = Generalized.inputs ops := by
    unfold Generalized.inputs
    rw [← List.flatMap_append, List.take_append_drop]
  have hnpre : (Generalized.inputs (ops.take m)).Nodup := (List.nodup_append.mp (he.symm ▸ hn)).1
  have hs : (Generalized.inputs (ops.take m)).Perm (emitted ++ middle) := by
    simpa [ht.inputs, ht.outputs] using ht.supply
  have hnd := List.nodup_append.mp (hs.nodup_iff.mp hnpre)
  have hmem : v ∈ middle ↔ v ∈ Generalized.inputs (ops.take m) ∧ v ∉ emitted := by
    constructor
    · intro hm
      refine ⟨hs.mem_iff.mpr (by simp [hm]), ?_⟩
      intro ho
      exact hnd.2.2 v ho v hm rfl
    · rintro ⟨hi, ho⟩
      have hm := hs.mem_iff.mp hi
      simpa [ho] using hm
  obtain ⟨hip, hop⟩ := h.complete_event_members hv
  rw [← ht.inputs, ← ht.outputs, mem_traceInputs, mem_traceOutputs,
    mem_take_iff_idxOf_lt hip m, mem_take_iff_idxOf_lt hop m] at hmem
  simpa [extractedEndpoints, Nat.not_lt] using hmem

/-- Complete extraction from an unchanged successful unique empty-to-empty raw
history. It preserves both chronological words and identifies every actual
prefix stack with exactly the active extracted intervals. -/
theorem run_extract_endpoints {r s : Nat} {ops : List RawOp} {output : List Nat}
    (h : Generalized.run r s ops [] = some ([], output)) (hn : (Generalized.inputs ops).Nodup) :
    ∃ events, ExactTrace r s ops [] events [] output ∧
      events.Nodup ∧ events.length = ops.length ∧
      traceInputs events = Generalized.inputs ops ∧ traceOutputs events = output ∧
      IntervalCritical.WellFormed (extractedEndpoints events) (Generalized.inputs ops) ∧
      (∀ v ∈ Generalized.inputs ops, (extractedEndpoints events).left v < ops.length ∧
        (extractedEndpoints events).right v < ops.length) ∧
      ∀ m middle emitted, Generalized.run r s (ops.take m) [] = some (middle, emitted) →
        ∀ v, v ∈ middle ↔ v ∈ Generalized.inputs ops ∧
          (extractedEndpoints events).left v < m ∧ m ≤ (extractedEndpoints events).right v := by
  obtain ⟨events, ht⟩ := run_exact_trace h
  refine ⟨events, ht, ht.complete_nodup hn, ht.length, ht.inputs, ht.outputs,
    ht.endpoint_wellFormed hn, fun _ hv => ht.endpoint_bounds hv, ?_⟩
  intro m middle emitted hp v
  by_cases hv : v ∈ Generalized.inputs ops
  · simpa [hv] using ht.prefix_active hn hp hv
  · have hm : v ∉ middle := fun hmem => hv (ht.prefix_held_mem_input hp hmem)
    simp [hv, hm]

#print axioms run_exact_trace
#print axioms ExactTrace.take
#print axioms mem_take_iff_idxOf_lt
#print axioms ExactTrace.endpoint_wellFormed
#print axioms ExactTrace.prefix_active
#print axioms run_extract_endpoints
end StackSorting.Generalized
