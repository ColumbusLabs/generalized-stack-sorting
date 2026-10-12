import GeneralizedCanonicalTrace

/-! Every permutation has valid canonical endpoints. Combined with the existing
literal-machine bridges, generation at the requested widths is exactly peeling.
A permissive-width history establishes only endpoint validity and word identity. -/
namespace StackSorting.Generalized
open List IntervalCritical

/-- Reading all tokens at the top is legal at any positive insertion width. -/
theorem Run.push_all {r s : Nat} (hr : 0 < r) (held input : List Nat) :
    Run r s held input [] (input.reverse ++ held) := by
  induction input generalizing held with
  | nil => simpa using Run.nil held
  | cons a input ih =>
    have hs : Step r s held [a] [] (a :: held) := Step.push [] held a hr
    simpa [List.reverse_cons, List.append_assoc] using Run.cons hs (ih (a :: held))

/-- A stack can emit any permutation of its contents when every current position
is within the removal width. This uses literal prefix-split pop steps. -/
theorem Run.pop_permutation {r s : Nat} {held output : List Nat}
    (hp : held.Perm output) (hb : held.length < s) : Run r s held [] output [] := by
  induction output generalizing held with
  | nil =>
    have he : held = [] := List.perm_nil.mp hp
    subst held
    exact .nil []
  | cons a output ih =>
    have ha : a ∈ held := hp.mem_iff.mpr (by simp)
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
    have hs : pre.length < s := by simp only [List.length_append, List.length_cons] at hb; omega
    have ht : (pre ++ post).Perm output := (List.perm_middle.symm.trans hp).cons_inv
    have hbt : (pre ++ post).length < s := by
      simp only [List.length_append, List.length_cons] at hb ⊢; omega
    simpa using Run.cons (Step.pop pre post a hs) (ih ht hbt)

/-- A permissive physical machine realizes every finite output permutation.
This auxiliary realization is used for canonical schedule validity, not as a
claim of feasibility at arbitrary requested widths. -/
theorem permutation_permissive_run {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) : Run 1 (n+1) [] (List.range n) output [] := by
  have pushes := Run.push_all (s := n+1) (by decide : 0 < 1) [] (List.range n)
  have hp' : ((List.range n).reverse ++ []).Perm output := by
    simpa using (List.reverse_perm (List.range n)).trans hp.symm
  have pops := Run.pop_permutation (r := 1) (s := n+1) hp' (by simp)
  simpa using pushes.append pops

/-- The deterministic canonical event list of every permutation has an actual
permissive-width exact trace with precisely the increasing input word. -/
theorem permutation_canonical_trace {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    ∃ ops, ExactTrace 1 (n+1) ops [] (canonicalEvents 0 output) [] output ∧
      Generalized.inputs ops = List.range n :=
  (generated_iff_canonical_trace 1 (n+1) n output).mp (permutation_permissive_run hp)

/-- Canonical endpoints and chronological words are valid for all permutations,
including those rejected by the widths eventually used for recognition. -/
theorem permutation_canonical_validity {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    (canonicalEvents 0 output).Nodup ∧
      traceInputs (canonicalEvents 0 output) = List.range n ∧
      traceOutputs (canonicalEvents 0 output) = output ∧
      WellFormed (extractedEndpoints (canonicalEvents 0 output)) (List.range n) ∧
      (∀ v ∈ List.range n,
        (extractedEndpoints (canonicalEvents 0 output)).right v < (canonicalEvents 0 output).length) ∧
      (∀ order, order.Perm (List.range n) →
        endpointInputs (extractedEndpoints (canonicalEvents 0 output)) order 0
          (canonicalEvents 0 output).length = List.range n ∧
        endpointOutputs (extractedEndpoints (canonicalEvents 0 output)) order 0
          (canonicalEvents 0 output).length = output) := by
  obtain ⟨ops, ht, hi⟩ := permutation_canonical_trace hp
  have hn : (Generalized.inputs ops).Nodup := by simpa [hi] using (List.nodup_range (n := n))
  refine ⟨ht.complete_nodup hn, ht.inputs.trans hi, ht.outputs,
    by simpa [hi] using ht.endpoint_wellFormed hn, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ Generalized.inputs ops := by simpa [hi] using hv
    simpa [ht.length] using (ht.endpoint_bounds hv').2
  · intro order ho
    have ho' : order.Perm (Generalized.inputs ops) := by simpa [hi] using ho
    simpa [ht.length, hi] using ht.endpoint_words hn ho'

/-- Exact canonical endpoint recognition of every ordinary output permutation.
Target-width feasibility is derived in the forward direction and supplied only
by peeling in the reverse direction; permissive validity cannot supply it. -/
theorem generated_iff_canonical_peelable {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) :
    Run r s [] (List.range n) output [] ↔
      Peelable (extractedEndpoints (canonicalEvents 0 output)) r s (List.range n) := by
  constructor
  · intro h
    exact (generated_canonical_peelable h).2
  · intro h
    obtain ⟨_, _, _, hw, hb, hwords⟩ := permutation_canonical_validity hp
    obtain ⟨order, ho, _, _, hr, hi⟩ := h.endpoint_history hw hb
    obtain ⟨hin, hout⟩ := hwords order ho
    rw [hout] at hr
    rw [hin] at hi
    simpa [hi] using run_relational r s _ [] [] output hr

#print axioms Run.push_all
#print axioms Run.pop_permutation
#print axioms permutation_permissive_run
#print axioms permutation_canonical_trace
#print axioms permutation_canonical_validity
#print axioms generated_iff_canonical_peelable
end StackSorting.Generalized
