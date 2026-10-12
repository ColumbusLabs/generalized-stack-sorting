import GeneralizedIntervalRecognition

/-! Recover the exact chronological words of the original successful history
from its extracted endpoint sweep, then replay those words in the literal machine.
No standardization, relabelling, input/output inversion, or schedule change occurs. -/
namespace StackSorting.Generalized
open List IntervalCritical

/-- Enumerating every list position in increasing order preserves its flat map. -/
theorem flatMap_positions (events : List EndpointEvent) (start : Nat)
    (f : Nat → List Nat) (g : EndpointEvent → List Nat)
    (h : ∀ i (hi : i < events.length), f (start+i) = g events[i]) :
    (List.range' start events.length).flatMap f = events.flatMap g := by
  induction events generalizing start with
  | nil => simp
  | cons event events ih =>
    have hz : f start = g event := by
      have h0 := h 0 (by simp)
      change f (start+0) = g event at h0
      simpa only [Nat.add_zero] using h0
    have ht : ∀ i (hi : i < events.length), f ((start+1)+i) = g events[i] := by
      intro i hi
      have hs := h (i+1) (by simpa using Nat.succ_lt_succ hi)
      change f (start+(i+1)) = g events[i] at hs
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    simpa [List.range'_succ, hz] using congrArg (g event ++ ·) (ih (start+1) ht)

/-- At each true original operation index, the extracted sweep has exactly the
same push/pop token word. The order may be any permutation of the original supply. -/
theorem ExactTrace.endpoint_owners_at {r s i : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output order : List Nat}
    (ht : ExactTrace r s ops [] events [] output) (hin : (Generalized.inputs ops).Nodup)
    (hp : order.Perm (Generalized.inputs ops)) (hi : i < events.length) :
    startsAt (extractedEndpoints events) order i = events[i].input ∧
      endsAt (extractedEndpoints events) order i = events[i].output := by
  have hnd := ht.complete_nodup hin
  have hw : WellFormed (extractedEndpoints events) order := (ht.endpoint_wellFormed hin).perm hp.symm
  have hm : events[i] ∈ events := List.getElem_mem hi
  cases he : events[i] with
  | push v =>
    have hev : EndpointEvent.push v ∈ events := by simpa [he] using hm
    have hvU : v ∈ Generalized.inputs ops := by
      have hv := (mem_traceInputs v events).mpr hev
      simpa [ht.inputs] using hv
    have hvO := hp.mem_iff.mpr hvU
    have hidx : (extractedEndpoints events).left v = i := by
      dsimp [extractedEndpoints]
      rw [← he]
      exact hnd.idxOf_getElem i hi
    simpa [hidx, EndpointEvent.input, EndpointEvent.output] using endpoint_owners_left hw hvO
  | pop v =>
    have hev : EndpointEvent.pop v ∈ events := by simpa [he] using hm
    have hvOut : v ∈ traceOutputs events := (mem_traceOutputs v events).mpr hev
    have hs : (traceInputs events).Perm (traceOutputs events) := by simpa using ht.supply
    have hvU : v ∈ Generalized.inputs ops := by simpa [ht.inputs] using hs.mem_iff.mpr hvOut
    have hvO := hp.mem_iff.mpr hvU
    have hidx : (extractedEndpoints events).right v = i := by
      dsimp [extractedEndpoints]
      rw [← he]
      exact hnd.idxOf_getElem i hi
    simpa [hidx, EndpointEvent.input, EndpointEvent.output] using endpoint_owners_right hw hvO

/-- Sweeping all extracted endpoint times recovers the exact original input and
output sequences, rather than merely their sets or permutation counts. -/
theorem ExactTrace.endpoint_words {r s : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output order : List Nat}
    (ht : ExactTrace r s ops [] events [] output) (hin : (Generalized.inputs ops).Nodup)
    (hp : order.Perm (Generalized.inputs ops)) :
    endpointInputs (extractedEndpoints events) order 0 ops.length = Generalized.inputs ops ∧
      endpointOutputs (extractedEndpoints events) order 0 ops.length = output := by
  have hi := flatMap_positions events 0 (startsAt (extractedEndpoints events) order) EndpointEvent.input
    (fun i h => by simpa using (ht.endpoint_owners_at hin hp h).1)
  have ho := flatMap_positions events 0 (endsAt (extractedEndpoints events) order) EndpointEvent.output
    (fun i h => by simpa using (ht.endpoint_owners_at hin hp h).2)
  change endpointInputs (extractedEndpoints events) order 0 events.length = traceInputs events at hi
  change endpointOutputs (extractedEndpoints events) order 0 events.length = traceOutputs events at ho
  rw [ht.length, ht.inputs] at hi
  rw [ht.length, ht.outputs] at ho
  exact ⟨hi, ho⟩

/-- An actual unique empty-to-empty history can be replayed by the explicit
endpoint program, retaining the original chronological token labels and words.
The endpoint witness and global order are constructed from the actual history. -/
theorem run_endpoint_replay {r s : Nat} {ops : List RawOp} {output : List Nat}
    (h : Generalized.run r s ops [] = some ([], output))
    (hin : (Generalized.inputs ops).Nodup) :
    ∃ events order, ExactTrace r s ops [] events [] output ∧
      events.length = ops.length ∧ traceInputs events = Generalized.inputs ops ∧
      traceOutputs events = output ∧ order.Perm (Generalized.inputs ops) ∧
      WellFormed (extractedEndpoints events) order ∧
      FeasibleEndpointOrder (extractedEndpoints events) r s order ∧
      Generalized.run r s (endpointProgram (extractedEndpoints events) order 0 ops.length) [] =
        some ([], output) ∧
      Generalized.inputs (endpointProgram (extractedEndpoints events) order 0 ops.length) =
        Generalized.inputs ops := by
  obtain ⟨events, order, ht, _, hlen, hinputs, houtputs, hw, _, hp, hf, _⟩ := run_extract_peelable h hin
  have hwo := hw.perm hp.symm
  have bound : ∀ v ∈ order, (extractedEndpoints events).right v < ops.length :=
    fun v hv => (ht.endpoint_bounds (hp.mem_iff.mp hv)).2
  obtain ⟨hr, hi⟩ := endpointProgram_complete hwo hf bound
  obtain ⟨hwi, hwo'⟩ := ht.endpoint_words hin hp
  rw [hwo'] at hr
  rw [hwi] at hi
  exact ⟨events, order, ht, hlen, hinputs, houtputs, hp, hwo, hf, hr, hi⟩

#print axioms flatMap_positions
#print axioms ExactTrace.endpoint_owners_at
#print axioms ExactTrace.endpoint_words
#print axioms run_endpoint_replay
end StackSorting.Generalized
