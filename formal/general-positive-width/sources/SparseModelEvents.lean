import SparseModelPermutation
import LazyEventConverse

namespace StackSorting.SparseEndpointMSO
open Generalized IntervalCritical
attribute [local instance] Classical.propDecidable

/-- Number of insertion events strictly before the time index x. -/
noncomputable def insertionRank (D : Model) (x : Nat) : Nat := by
  classical
  exact ((List.range x).filter (fun y => decide (D.I y))).length

theorem insertionRank_zero (D : Model) : insertionRank D 0 = 0 := by
  simp [insertionRank]

theorem insertionRank_succ (D : Model) (x : Nat) :
    insertionRank D (x + 1) = insertionRank D x + if D.I x then 1 else 0 := by
  classical
  by_cases hi : D.I x <;> simp [insertionRank, List.range_succ, hi]

theorem insertionRank_mono (D : Model) {x y : Nat} (h : x ≤ y) :
    insertionRank D x ≤ insertionRank D y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    rw [Nat.add_succ, insertionRank_succ]
    omega

theorem insertionRank_strict (D : Model) {x y : Nat} (hx : D.I x) (hxy : x < y) :
    insertionRank D x < insertionRank D y := by
  have hm := insertionRank_mono D (Nat.succ_le_of_lt hxy)
  rw [insertionRank_succ, ite_eq_left hx] at hm
  omega

theorem range_split_at_index {x length : Nat} (hx : x < length) :
    List.range length = List.range x ++ x :: List.range' (x + 1) (length - (x + 1)) := by
  have hc : x + (length - x) = length := by omega
  have hl : length - x = (length - (x + 1)) + 1 := by omega
  have he := List.range'_append (s := 0) (m := x) (n := length - x) (step := 1)
  rw [hc] at he
  rw [hl] at he
  simpa [List.range'_succ, ← List.range_eq_range'] using he.symm

theorem insertionRank_eq_idxOf {D : Model} {length x : Nat}
    (hp : TimePath D length) (hx : x ∈ D.domain) (hi : D.I x) :
    insertionRank D x = (insertionTokens D).idxOf x := by
  classical
  have hxl : x < length := by simpa [hp.1] using hx
  have hnot : x ∉ (List.range x).filter (fun y => decide (D.I y)) := by simp
  simp only [insertionTokens, hp.1, range_split_at_index hxl, List.filter_append,
    List.filter_cons, decide_eq_true hi, ite_true, List.idxOf_append, hnot, ite_false,
    List.idxOf_cons_self, Nat.zero_add, insertionRank]

noncomputable def modelEvent (D : Model) (x : Nat) : EndpointEvent := by
  classical
  exact if D.I x then .push (insertionRank D x)
    else .pop (insertionRank D (partner D x))

noncomputable def modelEvents (D : Model) : List EndpointEvent :=
  D.domain.map (modelEvent D)

theorem modelEvents_length (D : Model) : (modelEvents D).length = D.domain.length :=
  List.length_map _

theorem modelEvent_push_iff (D : Model) (x a : Nat) :
    modelEvent D x = .push a ↔ D.I x ∧ insertionRank D x = a := by
  classical
  by_cases h : D.I x <;> simp [modelEvent, h]

theorem modelEvent_pop_iff (D : Model) (x a : Nat) :
    modelEvent D x = .pop a ↔ ¬ D.I x ∧ insertionRank D (partner D x) = a := by
  classical
  by_cases h : D.I x <;> simp [modelEvent, h]

theorem modelEvents_get {D : Model} {length x : Nat}
    (hp : TimePath D length) (hx : x < length) :
    (modelEvents D)[x]? = some (modelEvent D x) := by
  simp [modelEvents, hp.1, hx]

theorem modelEvents_ranked_suffix {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) (count start : Nat)
    (hb : start + count ≤ length) :
    RankedForward (insertionRank D start)
      ((List.range' start count).map (modelEvent D)) := by
  classical
  induction count generalizing start with
  | zero => simpa using RankedForward.nil (insertionRank D start)
  | succ count ih =>
    have hx : start ∈ D.domain := by rw [hp.1, List.mem_range]; omega
    have htail := ih (start + 1) (by omega)
    rw [List.range'_succ, List.map_cons]
    by_cases hi : D.I start
    · rw [modelEvent, ite_eq_left hi]
      rw [insertionRank_succ, ite_eq_left hi] at htail
      exact .push htail
    · rw [modelEvent, ite_eq_right hi]
      have hr := (h.partition start hx).1.resolve_left hi
      obtain ⟨hpm, hm⟩ := partner_spec h hx
      have hpi := (partner_insert_iff_remove h hx).mpr hr
      have hlt := h.forward _ hpm start hx hpi (h.symmetric start hx _ hpm hm)
      rw [insertionRank_succ, ite_eq_right hi, Nat.add_zero] at htail
      exact .pop (insertionRank_strict D hpi hlt) htail

theorem modelEvents_ranked {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) : RankedForward 0 (modelEvents D) := by
  simpa [modelEvents, hp.1, insertionRank_zero, ← List.range_eq_range'] using
    modelEvents_ranked_suffix hp h length 0 (by omega)

theorem modelEvent_of_prefix {D : Model} {length : Nat}
    (hp : TimePath D length) {pre post : List EndpointEvent} {e : EndpointEvent}
    (he : modelEvents D = pre ++ e :: post) :
    pre.length < length ∧ modelEvent D pre.length = e := by
  have hlen := congrArg List.length he
  simp only [modelEvents_length, hp.1, List.length_range, List.length_append,
    List.length_cons] at hlen
  have hx : pre.length < length := by omega
  have hv := modelEvents_get hp hx
  rw [he] at hv
  have hsome : some e = some (modelEvent D pre.length) := by
    simpa [List.getElem?_append_right] using hv
  exact ⟨hx, (Option.some.inj hsome).symm⟩

theorem modelEvents_lazy {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) (hl : LazyBoundary D) :
    EventLazyBoundary (modelEvents D) := by
  intro pre a b post he
  obtain ⟨hx, hpush⟩ := modelEvent_of_prefix hp he
  have he' : modelEvents D = (pre ++ [.push a]) ++ .pop b :: post := by
    simpa [List.append_assoc] using he
  obtain ⟨hy, hpop⟩ := modelEvent_of_prefix hp he'
  simp only [List.length_append, List.length_singleton] at hy hpop
  obtain ⟨hi, hra⟩ := (modelEvent_push_iff _ _ _).mp hpush
  obtain ⟨hni, hrb⟩ := (modelEvent_pop_iff _ _ _).mp hpop
  have hxm : pre.length ∈ D.domain := by simpa [hp.1] using hx
  have hym : pre.length + 1 ∈ D.domain := by simpa [hp.1] using hy
  have hr := (h.partition _ hym).1.resolve_left hni
  have hm := hl _ hxm _ hym hi hr ((hp.2 _ hxm _ hym).mpr rfl)
  have hpart := partner_unique h hym hxm (h.symmetric _ hxm _ hym hm)
  rw [← hpart] at hrb
  exact hra.symm.trans hrb

theorem modelEvents_noTrailingPush {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) : NoTrailingPush (modelEvents D) := by
  intro pre a he
  obtain ⟨hx, hev⟩ := modelEvent_of_prefix hp he
  have hi := ((modelEvent_push_iff _ _ _).mp hev).1
  have hxm : pre.length ∈ D.domain := by simpa [hp.1] using hx
  obtain ⟨hpm, hm⟩ := partner_spec h hxm
  have hforward := h.forward _ hxm _ hpm hi hm
  have hbound : partner D pre.length < length := by simpa [hp.1] using hpm
  have hlen := congrArg List.length he
  simp only [modelEvents_length, hp.1, List.length_range, List.length_append,
    List.length_singleton] at hlen
  omega

theorem traceOutputs_modelEvents_map {D : Model} (h : MatchingAxioms D)
    (xs : List Nat) (hxs : ∀ x ∈ xs, x ∈ D.domain) :
    traceOutputs (xs.map (modelEvent D)) =
      (xs.filter (fun x => decide (D.R x))).map (fun x => insertionRank D (partner D x)) := by
  classical
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht := ih (fun y hy => hxs y (by simp [hy]))
    by_cases hi : D.I x
    · have hn : ¬ D.R x := fun hr => (h.partition x hx).2 ⟨hi, hr⟩
      simpa [List.map_cons, traceOutputs, List.flatMap_cons, modelEvent, hi,
        EndpointEvent.output, hn] using ht
    · have hr := (h.partition x hx).1.resolve_left hi
      simpa [List.map_cons, traceOutputs, List.flatMap_cons, modelEvent, hi,
        EndpointEvent.output, hr] using congrArg (insertionRank D (partner D x) :: ·) ht

theorem modelEvents_outputs {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) :
    traceOutputs (modelEvents D) = decodedPermutation D := by
  classical
  rw [modelEvents, traceOutputs_modelEvents_map h _ (fun _ hv => hv)]
  change (removalVertices D).map (fun x => insertionRank D (partner D x)) = _
  simp only [decodedPermutation, vertexOutput, List.map_map]
  apply List.map_congr_left
  intro x hx
  obtain ⟨hxm, hxr⟩ := (mem_removalVertices D x).mp hx
  exact insertionRank_eq_idxOf hp (partner_spec h hxm).1
    ((partner_insert_iff_remove h hxm).mpr hxr)

/-- The full chronological event word of an arbitrary time-indexed sparse
lazy matching equals the canonical word of its reconstructed permutation. -/
theorem modelEvents_eq_canonical {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) (hl : LazyBoundary D) :
    modelEvents D = canonicalEvents 0 (decodedPermutation D) := by
  rw [(modelEvents_ranked hp h).eq_canonicalEvents
    (modelEvents_lazy hp h hl) (modelEvents_noTrailingPush hp h), modelEvents_outputs hp h]

#print axioms insertionRank_eq_idxOf
#print axioms modelEvents_ranked
#print axioms modelEvents_lazy
#print axioms modelEvents_noTrailingPush
#print axioms modelEvents_outputs
#print axioms modelEvents_eq_canonical
end StackSorting.SparseEndpointMSO
