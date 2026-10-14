import SparseModelConverse

namespace StackSorting.SparseEndpointMSO
open Generalized IntervalCritical
attribute [local instance] Classical.propDecidable

theorem eventDiagram_rank_prefix (events : List EndpointEvent) (x : Nat) :
    insertionRank (eventDiagram events) x = (traceInputs (events.take x)).length := by
  induction x with
  | zero => simp [insertionRank_zero, traceInputs]
  | succ x ih =>
    rw [insertionRank_succ, ih, List.take_add_one]
    cases he : events[x]? with
    | none =>
      have hi : ¬ (eventDiagram events).I x := by
        rintro ⟨a, ha⟩; rw [he] at ha; cases ha
      simp [hi, traceInputs]
    | some e =>
      cases e with
      | push a =>
        have hi : (eventDiagram events).I x := ⟨a, he⟩
        simp [hi, traceInputs, EndpointEvent.input]
      | pop a =>
        have hi : ¬ (eventDiagram events).I x := by
          rintro ⟨b, hb⟩; rw [he] at hb; cases hb
        simp [hi, traceInputs, EndpointEvent.input]

/-- Increasing input fixes each push label from the sparse insertion colors. -/
theorem eventDiagram_rank_push {events : List EndpointEvent} {n x a : Nat}
    (hin : traceInputs events = List.range n)
    (he : events[x]? = some (.push a)) : insertionRank (eventDiagram events) x = a := by
  obtain ⟨hx, hval⟩ := List.getElem?_eq_some_iff.mp he
  have hsplit : events = events.take x ++ .push a :: events.drop (x + 1) := by
    rw [← hval, List.getElem_cons_drop hx, List.take_append_drop]
  have hi : List.range n = traceInputs (events.take x) ++ a :: traceInputs (events.drop (x + 1)) := by
    exact hin.symm.trans (by
      simpa [traceInputs, EndpointEvent.input] using congrArg traceInputs hsplit)
  have hv := List.getElem_of_append hi rfl
  simpa only [List.getElem_range, ← eventDiagram_rank_prefix] using hv

theorem canonicalMatchingAxioms {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) : MatchingAxioms (canonicalDiagram output) where
  partition _ hx := eventDiagram_partition _ hx
  symmetric _ _ _ _ hm := (eventDiagram_matching_symmetric _).mp hm
  perfect := canonical_perfect_matching hp
  opposite x _ y _ hm := by
    obtain ⟨a, hxy | hyx⟩ := hm
    · exact ⟨fun _ => ⟨a, hxy.2⟩, fun _ => ⟨a, hxy.1⟩⟩
    · constructor
      · rintro ⟨b, hb⟩
        have he := hb.symm.trans hyx.1
        cases he
      · rintro ⟨b, hb⟩
        have he := hb.symm.trans hyx.2
        cases he
  forward _ _ _ hy hi hm := canonical_matching_forward hp hi hy hm

/-- An arbitrary event list with increasing inputs and a genuine perfect
matching is recovered literally from its sparse diagram. -/
theorem modelEvents_eventDiagram {events : List EndpointEvent} {n : Nat}
    (hin : traceInputs events = List.range n) (h : MatchingAxioms (eventDiagram events)) :
    modelEvents (eventDiagram events) = events := by
  apply List.ext_getElem (by simp [modelEvents_length, eventDiagram])
  intro x hx hy
  have hm : x ∈ (eventDiagram events).domain := by simpa [eventDiagram] using hy
  have he : events[x]? = some events[x] := List.getElem?_eq_some_iff.mpr ⟨hy, rfl⟩
  have hme : (modelEvents (eventDiagram events))[x] = modelEvent (eventDiagram events) x := by
    simp [modelEvents, eventDiagram]
  rw [hme]
  cases hv : events[x] with
  | push a =>
    have hpush : events[x]? = some (.push a) := by simpa [hv] using he
    have hi : (eventDiagram events).I x := ⟨a, hpush⟩
    simp [modelEvent, hi, eventDiagram_rank_push hin hpush]
  | pop a =>
    have hpop : events[x]? = some (.pop a) := by simpa [hv] using he
    have hi : ¬ (eventDiagram events).I x := by
      rintro ⟨b, hb⟩; have he := hb.symm.trans hpop; cases he
    obtain ⟨_, hmatch⟩ := partner_spec h hm
    have hpartner : events[partner (eventDiagram events) x]? = some (.push a) := by
      obtain ⟨b, hxy | hyx⟩ := hmatch
      · have he := hpop.symm.trans hxy.1; cases he
      · have hab : a = b := EndpointEvent.pop.inj (Option.some.inj (hpop.symm.trans hyx.1))
        simpa [hab] using hyx.2
    simp [modelEvent, hi, eventDiagram_rank_push hin hpartner]

/-- Decoding is a left inverse on every actual canonical permutation diagram. -/
theorem decodedPermutation_canonical {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    decodedPermutation (canonicalDiagram output) = output := by
  have hin := (permutation_canonical_validity hp).2.1
  have hout := (permutation_canonical_validity hp).2.2.1
  have he := modelEvents_outputs (eventDiagram_path (canonicalEvents 0 output))
    (canonicalMatchingAxioms hp)
  rw [modelEvents_eventDiagram hin (canonicalMatchingAxioms hp), hout] at he
  exact he.symm

/-- Hence canonical diagrams never identify two different permutations. -/
theorem canonicalDiagram_injective {n m : Nat} {a b : List Nat}
    (ha : a.Perm (List.range n)) (hb : b.Perm (List.range m))
    (he : canonicalDiagram a = canonicalDiagram b) : a = b := by
  have hh := congrArg decodedPermutation he
  simpa only [decodedPermutation_canonical ha, decodedPermutation_canonical hb] using hh

/-- Full existence and uniqueness for arbitrary time-indexed lazy structures.
The explicit hypotheses are purely structural. -/
theorem sparseModel_exists_unique_permutation {D : Model} {length : Nat}
    (hp : TimePath D length) (h : MatchingAxioms D) (hl : LazyBoundary D) :
    ∃ output, output.Perm (List.range (insertionTokens D).length) ∧
      supported D = canonicalDiagram output ∧
      ∀ n other, other.Perm (List.range n) →
        supported D = canonicalDiagram other → other = output := by
  refine ⟨decodedPermutation D, decodedPermutation_perm hp h,
    supported_eq_canonicalDiagram hp h hl, ?_⟩
  intro n other ho he
  exact canonicalDiagram_injective ho (decodedPermutation_perm hp h)
    (he.symm.trans (supported_eq_canonicalDiagram hp h hl))

#print axioms modelEvents_eventDiagram
#print axioms decodedPermutation_canonical
#print axioms canonicalDiagram_injective
#print axioms sparseModel_exists_unique_permutation
end StackSorting.SparseEndpointMSO
