import GeneralizedCanonicalHeight

/-! Translate the actual bounded canonical history into the zero-based
generated-output displacement inequality, without assuming a maximum formula. -/
namespace StackSorting.Generalized
open List IntervalCritical

/-- Locate a specified occurrence in the chronological output word at its exact
pop event, retaining the whole preceding output word. -/
theorem traceOutputs_split {events : List EndpointEvent} {pre post : List Nat} {v : Nat}
    (h : traceOutputs events = pre ++ v :: post) :
    ∃ before after, events = before ++ .pop v :: after ∧ traceOutputs before = pre := by
  induction events generalizing pre with
  | nil => simp [traceOutputs] at h
  | cons event events ih =>
    cases event with
    | push a =>
      have ht : traceOutputs events = pre ++ v :: post := by simpa [traceOutputs, EndpointEvent.output] using h
      obtain ⟨before, after, he, ho⟩ := ih ht
      exact ⟨.push a :: before, after, by simp [he], by simp [traceOutputs, EndpointEvent.output] at ho ⊢; exact ho⟩
    | pop a =>
      cases pre with
      | nil =>
        have he : a = v ∧ traceOutputs events = post := by simpa [traceOutputs, EndpointEvent.output] using h
        exact ⟨[], events, by simp [he.1], rfl⟩
      | cons b pre =>
        have he : a = b ∧ traceOutputs events = pre ++ v :: post := by
          simpa [traceOutputs, EndpointEvent.output] using h
        obtain ⟨before, after, hsplit, hout⟩ := ih he.2
        exact ⟨.pop a :: before, after, by simp [hsplit], by simp [traceOutputs, EndpointEvent.output, he.1] at hout ⊢; exact hout⟩

/-- A chronological prefix of increasing input is exactly the initial range
of its own length, not merely a subset of the full input range. -/
theorem prefix_of_range {pre post : List Nat} {n : Nat}
    (h : pre ++ post = List.range n) : pre = List.range pre.length := by
  have hlen : pre.length ≤ n := by
    have he := congrArg List.length h
    simp only [List.length_append, List.length_range] at he
    omega
  have ht := congrArg (List.take pre.length) h
  simpa [List.take_left, Nat.min_eq_left hlen] using ht

/-- Any actual increasing-input history with all physical prefix stacks bounded
by B obeys v+1 ≤ i+B when value v is the output at zero-based position i. -/
theorem ExactTrace.output_value_le_prefix_height {p q n B : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output pre post : List Nat} {v : Nat}
    (ht : ExactTrace p q ops [] events [] output)
    (hi : Generalized.inputs ops = List.range n)
    (hheight : ∀ m middle emitted,
      Generalized.run p q (ops.take m) [] = some (middle, emitted) → middle.length ≤ B)
    (hout : output = pre ++ v :: post) : v+1 ≤ pre.length+B := by
  obtain ⟨beforeEvents, afterEvents, hsplit, hpre⟩ := traceOutputs_split (ht.outputs.trans hout)
  have hevent : events[beforeEvents.length]? = some (.pop v) := by
    rw [hsplit, List.getElem?_append_right (Nat.le_refl _)]
    simp
  obtain ⟨op, middle, after, emitted, _, hprefix, hstep, hinput, _⟩ := ht.event_at hevent
  have hemitted : emitted = pre := by
    have he := (ht.take_of_run hprefix).outputs
    have htake : events.take beforeEvents.length = beforeEvents := by simp [hsplit]
    rw [htake, hpre] at he
    exact he.symm
  have hvmid : v ∈ middle := by
    have hs : Step p q middle [] [v] after := by
      simpa only [hinput, EndpointEvent.input] using step_relational p q op middle after [v] hstep
    cases hs with
    | pop pre post v allowed => simp
  have hsp : (Generalized.inputs (ops.take beforeEvents.length)).Perm (emitted ++ middle) := by
    simpa using (run_relational p q _ [] middle emitted hprefix).supply
  have hvinput : v ∈ Generalized.inputs (ops.take beforeEvents.length) :=
    hsp.mem_iff.mpr (by simp [hvmid])
  have hcat : Generalized.inputs (ops.take beforeEvents.length) ++
      Generalized.inputs (ops.drop beforeEvents.length) = List.range n := by
    unfold Generalized.inputs
    rw [← List.flatMap_append, List.take_append_drop]
    exact hi
  have hread := prefix_of_range hcat
  have hvlt : v < (Generalized.inputs (ops.take beforeEvents.length)).length := by
    rw [hread] at hvinput
    exact List.mem_range.mp hvinput
  have hlen : (Generalized.inputs (ops.take beforeEvents.length)).length = emitted.length + middle.length := by
    simpa using hsp.length_eq
  have hb := hheight _ _ _ hprefix
  rw [hemitted] at hlen
  omega

/-- Generated-output displacement for an ordinary one-deletion-minimal rejected
permutation. Labels and positions are zero-based; no inversion is performed. -/
theorem oneDeletionMinimal_output_displacement {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] (List.range n) output [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (List.range (n-1)) (deleteWord v output) [])
    {pre post : List Nat} {v : Nat} (hout : output = pre ++ v :: post) :
    v ≤ pre.length + 2 * max r s := by
  obtain ⟨ops, ht, hi, hb⟩ := oneDeletionMinimal_canonical_history_height_le hp hr hs hreject hdelete
  have h := ht.output_value_le_prefix_height hi hb hout
  omega

/-- Index-based form: output[i] ≤ i + 2*max r s. For (3,3), displacement is at
most six, matching the separately proved physical lazy-height bound seven. -/
theorem oneDeletionMinimal_output_getElem_le {r s n i : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] (List.range n) output [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (List.range (n-1)) (deleteWord v output) []) (hi : i < output.length) :
    output[i] ≤ i + 2 * max r s := by
  have hsplit : output = output.take i ++ output[i] :: output.drop (i+1) := by
    rw [List.getElem_cons_drop hi, List.take_append_drop]
  have h := oneDeletionMinimal_output_displacement hp hr hs hreject hdelete hsplit
  simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] using h

#print axioms traceOutputs_split
#print axioms ExactTrace.output_value_le_prefix_height
#print axioms oneDeletionMinimal_output_displacement
#print axioms oneDeletionMinimal_output_getElem_le
end StackSorting.Generalized
