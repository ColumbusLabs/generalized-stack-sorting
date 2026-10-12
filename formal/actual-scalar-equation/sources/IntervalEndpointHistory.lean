import IntervalEndpointOrder

/-! A fixed chronological endpoint program in the existing executable machine.
An endpoint-free natural time contributes no operation. Consecutive endpoints
remain separate operations. This is the constructive scheduled direction only;
extraction from an arbitrary successful history is not proved here. -/
namespace StackSorting.IntervalCritical
open List

/-- Find the unique endpoint at `t`, retaining the prefix above its owner. -/
def operationAtAux (e : Endpoints) (above : Tokens) : Tokens → Nat → Option Generalized.RawOp
  | [], _ => none
  | v :: below, t =>
      if e.left v = t then some (.push (endpointCount e above t) v)
      else if e.right v = t then some (.pop (endpointCount e above t))
      else operationAtAux e (above ++ [v]) below t

def operationAt (e : Endpoints) (order : Tokens) (t : Nat) : Option Generalized.RawOp :=
  operationAtAux e [] order t

def startsAt (e : Endpoints) (order : Tokens) (t : Nat) : Tokens :=
  order.filter (fun v => decide (e.left v = t))

def endsAt (e : Endpoints) (order : Tokens) (t : Nat) : Tokens :=
  order.filter (fun v => decide (e.right v = t))

/-- The fixed raw program, with at most one operation at each natural event time. -/
def endpointProgram (e : Endpoints) (order : Tokens) (start count : Nat) : List Generalized.RawOp :=
  (List.range' start count).flatMap (fun t => (operationAt e order t).toList)

def endpointInputs (e : Endpoints) (order : Tokens) (start count : Nat) : Tokens :=
  (List.range' start count).flatMap (startsAt e order)

def endpointOutputs (e : Endpoints) (order : Tokens) (start count : Nat) : Tokens :=
  (List.range' start count).flatMap (endsAt e order)

theorem operationAtAux_skip (e : Endpoints) (above pre post : Tokens) (t : Nat)
    (h : ∀ v ∈ pre, e.left v ≠ t ∧ e.right v ≠ t) :
    operationAtAux e above (pre ++ post) t = operationAtAux e (above ++ pre) post t := by
  induction pre generalizing above with
  | nil => simp
  | cons v pre ih =>
    have hv := h v (by simp)
    have ht : ∀ u ∈ pre, e.left u ≠ t ∧ e.right u ≠ t :=
      fun u hu => h u (by simp [hu])
    simpa [operationAtAux, hv.1, hv.2, List.append_assoc] using ih (above ++ [v]) ht

theorem prefix_owner_ne {e : Endpoints} {order above below : Tokens} {v : Nat}
    (wf : WellFormed e order) (split : order = above ++ v :: below) :
    ∀ u ∈ above, u ≠ v := by
  have hn := List.nodup_append.mp (show (above ++ v :: below).Nodup by rw [← split]; exact wf.nodup)
  exact fun u hu => hn.2.2 u hu v (by simp)

/-- Every insertion endpoint selects exactly the owner's push and actual prefix slot. -/
theorem operationAt_left {e : Endpoints} {order above below : Tokens} {v : Nat}
    (wf : WellFormed e order) (split : order = above ++ v :: below) :
    operationAt e order (e.left v) = some (.push (endpointCount e above (e.left v)) v) := by
  have hv : v ∈ order := by simp [split]
  have hskip : ∀ u ∈ above, e.left u ≠ e.left v ∧ e.right u ≠ e.left v := by
    intro u hu
    have huO : u ∈ order := by simp [split, hu]
    refine ⟨?_, fun h => wf.cross_distinct v hv u huO h.symm⟩
    intro h
    exact prefix_owner_ne wf split u hu (wf.left_unique u huO v hv h)
  unfold operationAt
  rw [split, operationAtAux_skip e [] above (v :: below) (e.left v) hskip]
  simp [operationAtAux]

/-- Every removal endpoint selects exactly the owner's pop and actual prefix slot. -/
theorem operationAt_right {e : Endpoints} {order above below : Tokens} {v : Nat}
    (wf : WellFormed e order) (split : order = above ++ v :: below) :
    operationAt e order (e.right v) = some (.pop (endpointCount e above (e.right v))) := by
  have hv : v ∈ order := by simp [split]
  have hproper := wf.proper v hv
  have hskip : ∀ u ∈ above, e.left u ≠ e.right v ∧ e.right u ≠ e.right v := by
    intro u hu
    have huO : u ∈ order := by simp [split, hu]
    refine ⟨wf.cross_distinct u huO v hv, ?_⟩
    intro h
    exact prefix_owner_ne wf split u hu (wf.right_unique u huO v hv h)
  unfold operationAt
  rw [split, operationAtAux_skip e [] above (v :: below) (e.right v) hskip]
  simp [operationAtAux, Nat.ne_of_lt hproper]

theorem operationAt_none {e : Endpoints} {order : Tokens} {t : Nat}
    (h : ∀ v ∈ order, e.left v ≠ t ∧ e.right v ≠ t) : operationAt e order t = none := by
  have hs := operationAtAux_skip e [] order [] t h
  simpa [operationAt, operationAtAux] using hs

theorem filter_endpoint_singleton {f : Nat → Nat} {order : Tokens} {v : Nat}
    (hn : order.Nodup) (hv : v ∈ order)
    (hu : ∀ u ∈ order, f u = f v → u = v) :
    order.filter (fun u => decide (f u = f v)) = [v] := by
  have heq : order.filter (fun u => decide (f u = f v)) = order.filter (fun u => decide (u = v)) := by
    apply List.filter_congr
    intro u hum
    have he : f u = f v ↔ u = v := ⟨hu u hum, fun h => congrArg f h⟩
    simp only [he]
  rw [heq, List.filter_eq, hn.count_of_mem hv]
  rfl

theorem endpoint_owners_left {e : Endpoints} {order : Tokens} {v : Nat}
    (wf : WellFormed e order) (hv : v ∈ order) :
    startsAt e order (e.left v) = [v] ∧ endsAt e order (e.left v) = [] := by
  constructor
  · exact filter_endpoint_singleton wf.nodup hv (fun u hu => wf.left_unique u hu v hv)
  · apply List.filter_eq_nil_iff.mpr
    intro u hu
    simp only [decide_eq_true_eq]
    exact fun h => wf.cross_distinct v hv u hu h.symm

theorem endpoint_owners_right {e : Endpoints} {order : Tokens} {v : Nat}
    (wf : WellFormed e order) (hv : v ∈ order) :
    startsAt e order (e.right v) = [] ∧ endsAt e order (e.right v) = [v] := by
  constructor
  · apply List.filter_eq_nil_iff.mpr
    intro u hu
    simp only [decide_eq_true_eq]
    exact wf.cross_distinct u hu v hv
  · exact filter_endpoint_singleton wf.nodup hv (fun u hu => wf.right_unique u hu v hv)

/-- Adjacent natural-time states meet exactly, even when no event occurs. -/
theorem afterStack_eq_beforeStack_succ (e : Endpoints) (order : Tokens) (t : Nat) :
    afterStack e order t = beforeStack e order (t+1) := by
  apply List.filter_congr
  intro u hu
  have he : (e.left u ≤ t ∧ t < e.right u) ↔ (e.left u < t+1 ∧ t+1 ≤ e.right u) := by omega
  simp only [he]

/-- Every time slice runs the chosen actual operation (or no operation), and
introduces/emits exactly that time's endpoint owners. -/
theorem operationAt_run {e : Endpoints} {r s t : Nat} {order : Tokens}
    (wf : WellFormed e order) (hf : FeasibleEndpointOrder e r s order) :
    Generalized.run r s (operationAt e order t).toList (beforeStack e order t) =
      some (afterStack e order t, endsAt e order t) ∧
    Generalized.inputs (operationAt e order t).toList = startsAt e order t := by
  by_cases hl : ∃ v ∈ order, e.left v = t
  · obtain ⟨v, hv, rfl⟩ := hl
    obtain ⟨above, below, split⟩ := List.mem_iff_append.mp hv
    have hop := operationAt_left wf split
    have hs := (feasible_endpoint_raw_steps wf hf split).1
    obtain ⟨hi, ho⟩ := endpoint_owners_left wf hv
    simp [hop, hi, ho, Generalized.run, hs, Generalized.inputs, Generalized.introduced]
  · by_cases hr : ∃ v ∈ order, e.right v = t
    · obtain ⟨v, hv, rfl⟩ := hr
      obtain ⟨above, below, split⟩ := List.mem_iff_append.mp hv
      have hop := operationAt_right wf split
      have hs := (feasible_endpoint_raw_steps wf hf split).2
      obtain ⟨hi, ho⟩ := endpoint_owners_right wf hv
      simp [hop, hi, ho, Generalized.run, hs, Generalized.inputs, Generalized.introduced]
    · have hnone : ∀ v ∈ order, e.left v ≠ t ∧ e.right v ≠ t := by
        intro v hv
        exact ⟨fun h => hl ⟨v, hv, h⟩, fun h => hr ⟨v, hv, h⟩⟩
      have hop := operationAt_none hnone
      have hi : startsAt e order t = [] := List.filter_eq_nil_iff.mpr (by
        intro v hv; simpa using (hnone v hv).1)
      have ho : endsAt e order t = [] := List.filter_eq_nil_iff.mpr (by
        intro v hv; simpa using (hnone v hv).2)
      have heq : beforeStack e order t = afterStack e order t := by
        rw [beforeStack_eq_covering (fun v hv => (hnone v hv).2.symm),
          afterStack_eq_covering (fun v hv => (hnone v hv).1)]
      simp [hop, hi, ho, Generalized.run, Generalized.inputs, heq]

/-- The explicit chronological endpoint program executes through every slice. -/
theorem endpointProgram_run {e : Endpoints} {r s : Nat} {order : Tokens}
    (wf : WellFormed e order) (hf : FeasibleEndpointOrder e r s order)
    (start count : Nat) :
    Generalized.run r s (endpointProgram e order start count) (beforeStack e order start) =
      some (beforeStack e order (start+count), endpointOutputs e order start count) := by
  induction count generalizing start with
  | zero => simp [endpointProgram, endpointOutputs, Generalized.run]
  | succ count ih =>
    have hs := (operationAt_run (t := start) wf hf).1
    have ht := ih (start+1)
    simp only [endpointProgram] at ht
    simp [endpointProgram, endpointOutputs, List.range'_succ, Generalized.run_append,
      hs, afterStack_eq_beforeStack_succ, ht, Nat.add_comm, Nat.add_left_comm]

/-- The program's input word is the chronological list of insertion owners. -/
theorem endpointProgram_inputs {e : Endpoints} {r s : Nat} {order : Tokens}
    (wf : WellFormed e order) (hf : FeasibleEndpointOrder e r s order)
    (start count : Nat) :
    Generalized.inputs (endpointProgram e order start count) = endpointInputs e order start count := by
  induction count generalizing start with
  | zero => simp [endpointProgram, endpointInputs, Generalized.inputs]
  | succ count ih =>
    have hs := (operationAt_run (t := start) wf hf).2
    have ht := ih (start+1)
    simp only [Generalized.inputs, endpointProgram] at hs ht
    simp [endpointProgram, endpointInputs, List.range'_succ, Generalized.inputs, List.flatMap_append, hs, ht]

theorem beforeStack_zero (e : Endpoints) (order : Tokens) : beforeStack e order 0 = [] := by
  simp [beforeStack]

theorem beforeStack_empty_after {e : Endpoints} {order : Tokens} {limit : Nat}
    (bound : ∀ v ∈ order, e.right v < limit) : beforeStack e order limit = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro v hv
  have hb := bound v hv
  simp only [decide_eq_true_eq]
  omega

/-- If every removal event precedes `limit`, the complete fixed endpoint program
starts and ends empty and has exactly the chronological insertion/output words. -/
theorem endpointProgram_complete {e : Endpoints} {r s limit : Nat} {order : Tokens}
    (wf : WellFormed e order) (hf : FeasibleEndpointOrder e r s order)
    (bound : ∀ v ∈ order, e.right v < limit) :
    Generalized.run r s (endpointProgram e order 0 limit) [] =
        some ([], endpointOutputs e order 0 limit) ∧
    Generalized.inputs (endpointProgram e order 0 limit) = endpointInputs e order 0 limit := by
  refine ⟨?_, endpointProgram_inputs wf hf 0 limit⟩
  simpa [beforeStack_zero, beforeStack_empty_after bound] using endpointProgram_run wf hf 0 limit

/-- Successful endpoint peeling constructs this explicit fixed-endpoint literal
history. The chosen order changes only physical slots; the endpoint chronology
is determined by the given natural endpoints. No reverse extraction is assumed. -/
theorem Peelable.endpoint_history {e : Endpoints} {r s limit : Nat} {U : Tokens}
    (h : Peelable e r s U) (wf : WellFormed e U)
    (bound : ∀ v ∈ U, e.right v < limit) :
    ∃ order, order.Perm U ∧ WellFormed e order ∧ FeasibleEndpointOrder e r s order ∧
      Generalized.run r s (endpointProgram e order 0 limit) [] =
        some ([], endpointOutputs e order 0 limit) ∧
      Generalized.inputs (endpointProgram e order 0 limit) = endpointInputs e order 0 limit := by
  obtain ⟨order, hp, hwo, hfo⟩ := h.wellFormed_feasible_order wf
  have hb : ∀ v ∈ order, e.right v < limit := fun v hv => bound v (hp.mem_iff.mp hv)
  obtain ⟨hr, hi⟩ := endpointProgram_complete hwo hfo hb
  exact ⟨order, hp, hwo, hfo, hr, hi⟩

#print axioms operationAt_left
#print axioms operationAt_right
#print axioms operationAt_run
#print axioms endpointProgram_run
#print axioms endpointProgram_inputs
#print axioms endpointProgram_complete
#print axioms Peelable.endpoint_history
end StackSorting.IntervalCritical
