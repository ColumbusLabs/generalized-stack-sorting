import GeneralizedEndpointTrace

/-! Compose exact-history endpoint extraction with the actual global physical
order, proving that the extracted interval system is endpoint-peelable. No basis
criticality or final permutation-width theorem is assumed or proved here. -/
namespace StackSorting.Generalized
open List IntervalCritical

/-- Expose the actual raw operation and adjacent prefix states at an event index. -/
theorem ExactTrace.event_at {r s m : Nat} {ops : List RawOp}
    {held final output : List Nat} {events : List EndpointEvent} {event : EndpointEvent}
    (h : ExactTrace r s ops held events final output) (he : events[m]? = some event) :
    ∃ op before after emitted,
      ops[m]? = some op ∧
      Generalized.run r s (ops.take m) held = some (before, emitted) ∧
      step r s op before = some (after, event.output) ∧ introduced op = event.input ∧
      Generalized.run r s (ops.take (m+1)) held = some (after, emitted ++ event.output) := by
  induction h generalizing m event with
  | nil => simp at he
  | @cons op ops held middle final output ev events hs hi ht ih =>
    cases m with
    | zero =>
      simp at he
      subst event
      exact ⟨op, held, middle, [], by simp, rfl, hs, hi, by simp [Generalized.run, hs]⟩
    | succ m =>
      have he' : events[m]? = some event := by simpa using he
      obtain ⟨nextOp, before, after, emitted, hop, hp, hn, hin, hp'⟩ := ih he'
      refine ⟨nextOp, before, after, ev.output ++ emitted, by simpa using hop, ?_, hn, hin, ?_⟩
      · simp [Generalized.run, hs, hp]
      · simp [Generalized.run, hs, hp', List.append_assoc]

/-- A physical sublist of a duplicate-free order equals its membership filter. -/
theorem sublist_eq_filter {held order : List Nat} {p : Nat → Bool}
    (hn : order.Nodup) (hs : held <+ order)
    (hm : ∀ v ∈ order, p v ↔ v ∈ held) : held = order.filter p := by
  have hself : held.filter p = held := List.filter_eq_self.mpr (by
    intro v hv
    exact (hm v (hs.subset hv)).mpr hv)
  have hsub : held <+ order.filter p := by
    have hh := hs.filter p
    rw [hself] at hh
    exact hh
  have hlength : (order.filter p).length ≤ held.length := List.Nodup.length_le_of_subset (hn.filter p) (by
    intro v hv
    obtain ⟨hvo, hp⟩ := List.mem_filter.mp hv
    exact (hm v hvo).mp hp)
  exact hsub.eq_of_length_le hlength

/-- Given the global order produced from this exact raw history, the actual
prefix stack is exactly the extracted endpoint `beforeStack`. -/
theorem exact_prefix_eq_beforeStack {r s m : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output middle emitted order : List Nat}
    (ht : ExactTrace r s ops [] events [] output) (hin : (Generalized.inputs ops).Nodup)
    (horder : order.Nodup) (hperm : order.Perm (Generalized.inputs ops))
    (hsub : middle <+ order)
    (hp : Generalized.run r s (ops.take m) [] = some (middle, emitted)) :
    middle = beforeStack (extractedEndpoints events) order m := by
  apply sublist_eq_filter horder hsub
  intro v hv
  have hsource := hperm.mem_iff.mp hv
  simpa [beforeStack] using (ht.prefix_active hin hp hsource).symm

theorem idxOf_split_of_nodup {pre post : List Nat} {v : Nat}
    (hn : (pre ++ v :: post).Nodup) : (pre ++ v :: post).idxOf v = pre.length := by
  have hparts := List.nodup_append.mp hn
  have hnot : v ∉ pre := fun hv => hparts.2.2 v hv v (by simp) rfl
  simp [List.idxOf_append, hnot]

/-- Actual literal push legality bounds the inserted token's unique rank. -/
theorem Step.push_rank_bound {r s v : Nat} {before after : List Nat}
    (h : Step r s before [v] [] after) (hn : after.Nodup) : after.idxOf v < r := by
  cases h with
  | push pre post v allowed => rw [idxOf_split_of_nodup hn]; exact allowed

/-- Actual literal pop legality bounds the removed token's unique rank. -/
theorem Step.pop_rank_bound {r s v : Nat} {before after : List Nat}
    (h : Step r s before [] [v] after) (hn : before.Nodup) : before.idxOf v < s := by
  cases h with
  | pop pre post v allowed => rw [idxOf_split_of_nodup hn]; exact allowed

/-- The global order's prefix bounds follow from the actual operation slots at
the extracted events. Feasibility is a conclusion, not an input hypothesis. -/
theorem extracted_global_order_feasible {r s : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output order : List Nat}
    (ht : ExactTrace r s ops [] events [] output) (hin : (Generalized.inputs ops).Nodup)
    (horder : order.Nodup) (hperm : order.Perm (Generalized.inputs ops))
    (hprefix : ∀ m middle emitted,
      Generalized.run r s (ops.take m) [] = some (middle, emitted) → middle <+ order) :
    FeasibleEndpointOrder (extractedEndpoints events) r s order := by
  let e := extractedEndpoints events
  have wf : WellFormed e order := (ht.endpoint_wellFormed hin).perm hperm.symm
  apply (feasibleOrder_iff_prefixes e r s order).mpr
  intro above v below split
  have hvO : v ∈ order := by simp [split]
  have hv : v ∈ Generalized.inputs ops := hperm.mem_iff.mp hvO
  obtain ⟨hi, ho⟩ := ht.complete_event_members hv
  have hiGet : events[e.left v]? = some (.push v) := by
    dsimp [e, extractedEndpoints]
    rw [getElem?_eq_getElem (List.idxOf_lt_length_of_mem hi), List.getElem_idxOf]
  have hoGet : events[e.right v]? = some (.pop v) := by
    dsimp [e, extractedEndpoints]
    rw [getElem?_eq_getElem (List.idxOf_lt_length_of_mem ho), List.getElem_idxOf]
  obtain ⟨hbl, hal, hbr, har⟩ := endpoint_stack_splits wf split
  constructor
  · obtain ⟨op, before, after, emitted, _, hp, hs, hinput, hp'⟩ := ht.event_at hiGet
    have hrel : Step r s before [v] [] after := by
      have hh := step_relational r s op before after [] hs
      simpa [hinput, EndpointEvent.input] using hh
    have hafter : after = afterStack e order (e.left v) := by
      have heq := exact_prefix_eq_beforeStack ht hin horder hperm
        (hprefix _ _ _ hp') hp'
      simpa [← afterStack_eq_beforeStack_succ] using heq
    have hafterN : after.Nodup := by rw [hafter]; exact horder.filter _
    have hbound := hrel.push_rank_bound hafterN
    have hsplitN : (coveringList e above (e.left v) ++ v :: coveringList e below (e.left v)).Nodup := by
      rw [← hal]
      exact horder.filter _
    rw [hafter, hal, idxOf_split_of_nodup hsplitN] at hbound
    simpa [endpointCount, coveringList, List.countP_eq_length_filter] using hbound
  · obtain ⟨op, before, after, emitted, _, hp, hs, hinput, hp'⟩ := ht.event_at hoGet
    have hrel : Step r s before [] [v] after := by
      have hh := step_relational r s op before after [v] hs
      simpa [hinput, EndpointEvent.input] using hh
    have hbefore : before = beforeStack e order (e.right v) :=
      exact_prefix_eq_beforeStack ht hin horder hperm (hprefix _ _ _ hp) hp
    have hbeforeN : before.Nodup := by rw [hbefore]; exact horder.filter _
    have hbound := hrel.pop_rank_bound hbeforeN
    have hsplitN : (coveringList e above (e.right v) ++ v :: coveringList e below (e.right v)).Nodup := by
      rw [← hbr]
      exact horder.filter _
    rw [hbefore, hbr, idxOf_split_of_nodup hsplitN] at hbound
    simpa [endpointCount, coveringList, List.countP_eq_length_filter] using hbound

/-- Full reverse composition for an exact successful unique empty-to-empty raw
history: its actual endpoint indices admit a feasible order and are peelable.
The original chronological input/output words remain unchanged. -/
theorem run_extract_peelable {r s : Nat} {ops : List RawOp} {output : List Nat}
    (h : Generalized.run r s ops [] = some ([], output))
    (hin : (Generalized.inputs ops).Nodup) :
    ∃ events order, ExactTrace r s ops [] events [] output ∧
      events.Nodup ∧ events.length = ops.length ∧
      traceInputs events = Generalized.inputs ops ∧ traceOutputs events = output ∧
      WellFormed (extractedEndpoints events) (Generalized.inputs ops) ∧
      order.Nodup ∧ order.Perm (Generalized.inputs ops) ∧
      FeasibleEndpointOrder (extractedEndpoints events) r s order ∧
      Peelable (extractedEndpoints events) r s (Generalized.inputs ops) := by
  obtain ⟨events, ht⟩ := run_exact_trace h
  obtain ⟨order, hn, hp, hall⟩ := run_global_order_all_prefixes h (by simpa using hin)
  simp only [List.nil_append] at hp
  have hprefix : ∀ m middle emitted,
      Generalized.run r s (ops.take m) [] = some (middle, emitted) → middle <+ order := by
    intro m middle emitted hr
    exact hall (ops.take m) (ops.drop m) (List.take_append_drop m ops).symm middle emitted hr
  have hf := extracted_global_order_feasible ht hin hn hp hprefix
  have hpeel : Peelable (extractedEndpoints events) r s (Generalized.inputs ops) :=
    (peelable_iff_feasible_endpoint_order hin).mpr ⟨order, hp, hf⟩
  exact ⟨events, order, ht, ht.complete_nodup hin, ht.length, ht.inputs, ht.outputs,
    ht.endpoint_wellFormed hin, hn, hp, hf, hpeel⟩

#print axioms ExactTrace.event_at
#print axioms exact_prefix_eq_beforeStack
#print axioms extracted_global_order_feasible
#print axioms run_extract_peelable
end StackSorting.Generalized
