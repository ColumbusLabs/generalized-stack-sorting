import GeneralizedEndpointReplay
import GeneralizedRangeLazy

/-! Tie the deterministic lazy push/pop token schedule directly to the existing
RangeLazyRun normalization and actual executable slot-indexed histories. -/
namespace StackSorting.Generalized
open List IntervalCritical

/-- The first unread input is `next`. A held output causes only a pop; a new
record reads the increasing input through that record and immediately pops it. -/
def canonicalEvents (next : Nat) : List Nat → List EndpointEvent
  | [] => []
  | a :: output =>
    if a < next then .pop a :: canonicalEvents next output
    else (List.range' next (a+1-next)).map EndpointEvent.push ++
      .pop a :: canonicalEvents (a+1) output

theorem ExactTrace.append {r s : Nat} {ops ops' : List RawOp}
    {held middle final output output' : List Nat} {events events' : List EndpointEvent}
    (h : ExactTrace r s ops held events middle output)
    (h' : ExactTrace r s ops' middle events' final output') :
    ExactTrace r s (ops ++ ops') held (events ++ events') final (output ++ output') := by
  induction h with
  | nil => simpa using h'
  | cons hs hi _ ih => simpa [List.append_assoc] using ExactTrace.cons hs hi (ih h')

theorem events_eq_pushes_of_outputs_nil (events : List EndpointEvent)
    (h : traceOutputs events = []) : events = (traceInputs events).map EndpointEvent.push := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    cases event with
    | push a =>
      have ht : traceOutputs events = [] := by simpa [traceOutputs, EndpointEvent.output] using h
      simpa [traceInputs, EndpointEvent.input] using congrArg (EndpointEvent.push a :: ·) (ih ht)
    | pop a => simp [traceOutputs, EndpointEvent.output] at h

/-- A no-output segment of the established relational machine has exactly the
input tokens as its push-only event trace, in the original order. -/
theorem Run.pushes_exactTrace {r s : Nat} {held input final : List Nat}
    (h : Run r s held input [] final) :
    ∃ ops, ExactTrace r s ops held (input.map EndpointEvent.push) final [] ∧
      Generalized.inputs ops = input := by
  obtain ⟨ops, hr, hi⟩ := h.executable
  obtain ⟨events, ht⟩ := run_exact_trace hr
  have he := events_eq_pushes_of_outputs_nil events ht.outputs
  rw [ht.inputs, hi] at he
  exact ⟨ops, by simpa [he] using ht, hi⟩

/-- Canonical lazy normalization preserves the literal increasing input and
output words and realizes exactly the deterministic token event list. -/
theorem RangeLazyRun.exactTrace {r s limit next : Nat} {held output : List Nat}
    (h : RangeLazyRun r s limit next held output)
    (hb : ∀ v ∈ held, v < next) :
    ∃ ops, ExactTrace r s ops held (canonicalEvents next output) [] output ∧
      Generalized.inputs ops = List.range' next (limit-next) := by
  induction h with
  | nil => exact ⟨[], .nil [], by simp [Generalized.inputs]⟩
  | @held next a held after output pop tail ih =>
    have ha : a ∈ held := by
      have hx := pop.supply.mem_iff.mpr (by simp : a ∈ [a] ++ after)
      simpa using hx
    have hlt := hb a ha
    have hba : ∀ v ∈ after, v < next := by
      intro v hv
      have hx := pop.supply.mem_iff.mpr (by simp [hv] : v ∈ [a] ++ after)
      exact hb v (by simpa using hx)
    obtain ⟨ops, ht, hi⟩ := ih hba
    obtain ⟨op, hs, hin⟩ := pop.executable
    refine ⟨op :: ops, ?_, ?_⟩
    · simpa [canonicalEvents, hlt, EndpointEvent.input, EndpointEvent.output] using
        (ExactTrace.cons (event := EndpointEvent.pop a) hs hin ht)
    · simpa [Generalized.inputs, hin] using hi
  | @record next a held before after output lower upper fresh read pop tail ih =>
    have hbb : ∀ v ∈ before, v < a+1 := by
      intro v hv
      have hx : v ∈ held ++ List.range' next (a+1-next) :=
        read.supply.mem_iff.mpr (by simpa using hv)
      rcases List.mem_append.mp hx with hh | hr
      · have := hb v hh; omega
      · have := List.mem_range'.mp hr; omega
    have hba : ∀ v ∈ after, v < a+1 := by
      intro v hv
      have hx := pop.supply.mem_iff.mpr (by simp [hv] : v ∈ [a] ++ after)
      exact hbb v (by simpa using hx)
    obtain ⟨ops, ht, hi⟩ := ih hba
    obtain ⟨reads, hread, hri⟩ := read.pushes_exactTrace
    obtain ⟨op, hs, hin⟩ := pop.executable
    have hpop : ExactTrace r s (op :: ops) before
        (.pop a :: canonicalEvents (a+1) output) [] (a :: output) :=
      ExactTrace.cons hs hin ht
    have hstart : next + 1 * (a+1-next) = a+1 := by omega
    have hcount : a+1-next + (limit-(a+1)) = limit-next := by omega
    have hrange : List.range' next (a+1-next) ++ List.range' (a+1) (limit-(a+1)) =
        List.range' next (limit-next) := by
      simpa only [hstart, hcount] using
        (List.range'_append (s := next) (m := a+1-next) (n := limit-(a+1)) (step := 1))
    refine ⟨reads ++ op :: ops, ?_, ?_⟩
    · simpa [canonicalEvents, Nat.not_lt.mpr lower] using hread.append hpop
    · change (reads ++ op :: ops).flatMap introduced = _
      rw [List.flatMap_append, List.flatMap_cons]
      change Generalized.inputs reads ++ (introduced op ++ Generalized.inputs ops) = _
      rw [hri, hin, hi]
      simpa using hrange

/-- Every increasing-input generation has an actual raw history with exactly
the canonical lazy event trace; the converse is the existing raw machine. -/
theorem generated_iff_canonical_trace (r s n : Nat) (output : List Nat) :
    Run r s [] (List.range n) output [] ↔
      ∃ ops, ExactTrace r s ops [] (canonicalEvents 0 output) [] output ∧
        Generalized.inputs ops = List.range n := by
  constructor
  · intro h
    obtain ⟨ops, ht, hi⟩ := (generated_rangeLazy h).exactTrace (by simp)
    exact ⟨ops, ht, by simpa [List.range_eq_range'] using hi⟩
  · rintro ⟨ops, ht, hi⟩
    simpa [hi] using run_relational r s ops [] [] output ht.run

/-- Successful generation makes the *canonical*, not an arbitrary chosen,
lazy endpoint system well formed and peelable on the original input labels. -/
theorem generated_canonical_peelable {r s n : Nat} {output : List Nat}
    (h : Run r s [] (List.range n) output []) :
    WellFormed (extractedEndpoints (canonicalEvents 0 output)) (List.range n) ∧
      Peelable (extractedEndpoints (canonicalEvents 0 output)) r s (List.range n) := by
  obtain ⟨ops, ht, hi⟩ := (generated_iff_canonical_trace r s n output).mp h
  have hn : (Generalized.inputs ops).Nodup := by simpa [hi] using (List.nodup_range (n := n))
  have hw := ht.endpoint_wellFormed hn
  obtain ⟨order, hnd, hp, hall⟩ := run_global_order_all_prefixes ht.run (by simpa using hn)
  simp only [List.nil_append] at hp
  have hprefix : ∀ m middle emitted,
      Generalized.run r s (ops.take m) [] = some (middle, emitted) → middle <+ order := by
    intro m middle emitted hr
    exact hall (ops.take m) (ops.drop m) (List.take_append_drop m ops).symm middle emitted hr
  have hf := extracted_global_order_feasible ht hn hnd hp hprefix
  have hpeel := (peelable_iff_feasible_endpoint_order hn).mpr ⟨order, hp, hf⟩
  exact ⟨by simpa [hi] using hw, by simpa [hi] using hpeel⟩

#print axioms ExactTrace.append
#print axioms Run.pushes_exactTrace
#print axioms RangeLazyRun.exactTrace
#print axioms generated_iff_canonical_trace
#print axioms generated_canonical_peelable
end StackSorting.Generalized
