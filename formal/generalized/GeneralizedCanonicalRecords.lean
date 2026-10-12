import GeneralizedCanonicalRecognition

/-! Remove and restore the actual record intervals of the canonical lazy
schedule. Positive slot widths are explicit; no permutation deletion is used. -/
namespace StackSorting.IntervalCritical
open List

theorem endpointCount_filter_le (e : Endpoints) (U : Tokens) (keep : Nat → Bool) (t : Nat) :
    endpointCount e (U.filter keep) t ≤ endpointCount e U t := by
  induction U with
  | nil => simp [endpointCount]
  | cons a U ih =>
    cases hk : keep a <;> cases hc : decide (Covers e a t) <;>
      simp [endpointCount, hk, hc] at ih ⊢ <;> omega

/-- Removing arbitrary tokens cannot obstruct an existing peeling sequence. -/
theorem Peelable.filter {e : Endpoints} {r s : Nat} {U : Tokens}
    (h : Peelable e r s U) (keep : Nat → Bool) : Peelable e r s (U.filter keep) := by
  induction h with
  | nil => exact .nil
  | @step U v hv he rest ih =>
    by_cases hk : keep v = true
    · have hel : Eligible e r s (U.filter keep) v :=
        ⟨Nat.lt_of_le_of_lt (endpointCount_filter_le e U keep (e.left v)) he.1,
         Nat.lt_of_le_of_lt (endpointCount_filter_le e U keep (e.right v)) he.2⟩
      exact .step v (List.mem_filter.mpr ⟨hv, hk⟩) hel (by simpa [List.erase_filter] using ih)
    · have hvn : v ∉ U.filter keep := by simp [List.mem_filter, hk]
      simpa [← List.erase_filter, List.erase_of_not_mem hvn] using ih

theorem endpointCount_zero_of_vanishing {e : Endpoints} {U : Tokens}
    (h : ∀ v ∈ U, ∀ t, ¬ Covers e v t) (t : Nat) : endpointCount e U t = 0 := by
  apply List.countP_eq_zero.mpr
  intro v hv
  simpa using h v hv t

/-- An above-prefix of intervals with no integer interior changes no rank. -/
theorem feasibleAbove_prepend_vanishing {e : Endpoints} {r s : Nat} {W : Tokens}
    (hz : ∀ t, endpointCount e W t = 0) (above order : Tokens) :
    FeasibleAbove e r s (W ++ above) order ↔ FeasibleAbove e r s above order := by
  induction order generalizing above with
  | nil => simp [FeasibleAbove]
  | cons v order ih =>
    have hcount (t : Nat) : endpointCount e (W ++ above) t = endpointCount e above t := by
      simp only [endpointCount, List.countP_append] at hz ⊢
      rw [hz]; simp
    simp only [FeasibleAbove, Eligible, hcount, List.append_assoc, ih]

/-- Vanishing intervals can all be placed above the remaining order, where
both their insertion and removal prefix ranks are zero. -/
theorem feasibleOrder_vanishing {e : Endpoints} {r s : Nat} {W : Tokens}
    (hr : 0 < r) (hs : 0 < s) (hv : ∀ v ∈ W, ∀ t, ¬ Covers e v t) :
    FeasibleEndpointOrder e r s W := by
  apply (feasibleOrder_iff_prefixes e r s W).mpr
  intro above v below he
  have hz (t : Nat) : endpointCount e above t = 0 :=
    endpointCount_zero_of_vanishing (fun u hu => hv u (by simp [he, hu])) t
  simp [Eligible, hz, hr, hs]

/-- Exact restoration of every discarded zero-interior interval, for positive
widths. In particular a discarded record may lie inside a retained interval. -/
theorem peelable_iff_filter_vanishing {e : Endpoints} {r s : Nat} {U : Tokens}
    (hn : U.Nodup) (hr : 0 < r) (hs : 0 < s) (keep : Nat → Bool)
    (hv : ∀ v ∈ U, keep v = false → ∀ t, ¬ Covers e v t) :
    Peelable e r s U ↔ Peelable e r s (U.filter keep) := by
  constructor
  · exact fun h => h.filter keep
  · intro h
    let W := U.filter (fun v => !keep v)
    have hW : ∀ v ∈ W, ∀ t, ¬ Covers e v t := by
      intro v hm
      have hh := List.mem_filter.mp hm
      exact hv v hh.1 (by simpa using hh.2)
    have hz := endpointCount_zero_of_vanishing hW
    obtain ⟨order, hp, hf⟩ := h.feasible_order (hn.filter keep)
    have hwf := feasibleOrder_vanishing hr hs hW
    have hrest : FeasibleAbove e r s W order := by
      simpa using (feasibleAbove_prepend_vanishing hz [] order).mpr hf
    have hfull : FeasibleEndpointOrder e r s (W ++ order) :=
      (feasibleAbove_append e r s [] W order).mpr ⟨hwf, by simpa using hrest⟩
    have hpfull : (W ++ order).Perm U := by
      apply (List.Perm.append_left W hp).trans
      simpa [W] using List.filter_append_perm (fun v => !keep v) U
    exact (peelable_iff_feasible_endpoint_order hn).mpr ⟨W ++ order, hpfull, hfull⟩

/-- Discarding vanishing intervals preserves every endpoint count, not just
counts evaluated at endpoints of surviving tokens. -/
theorem endpointCount_filter_vanishing {e : Endpoints} {U : Tokens} (keep : Nat → Bool)
    (hv : ∀ v ∈ U, keep v = false → ∀ t, ¬ Covers e v t) (t : Nat) :
    endpointCount e (U.filter keep) t = endpointCount e U t := by
  induction U with
  | nil => rfl
  | cons v U ih =>
    have ht : ∀ w ∈ U, keep w = false → ∀ t, ¬ Covers e w t := fun w hw => hv w (by simp [hw])
    cases hk : keep v with
    | false =>
      have hc := hv v (by simp) hk t
      simpa [endpointCount, hk, hc] using ih ht
    | true => simpa [endpointCount, hk, List.countP_cons] using ih ht

end StackSorting.IntervalCritical

namespace StackSorting.Generalized
open List IntervalCritical

/-- Record outputs, using exactly the first-unread-input branch of the canonical
schedule. This definition keeps original token labels. -/
def canonicalRecords (next : Nat) : List Nat → List Nat
  | [] => []
  | a :: output =>
    if a < next then canonicalRecords next output
    else a :: canonicalRecords (a+1) output

/-- Every actual canonical record owns a consecutive push/pop pair. -/
theorem canonical_record_adjacent {next v : Nat} {output : List Nat}
    (hv : v ∈ canonicalRecords next output) :
    ∃ pre post, canonicalEvents next output = pre ++ .push v :: .pop v :: post := by
  induction output generalizing next with
  | nil => simp [canonicalRecords] at hv
  | cons a output ih =>
    by_cases ha : a < next
    · have ht : v ∈ canonicalRecords next output := by simpa [canonicalRecords, ha] using hv
      obtain ⟨pre, post, he⟩ := ih ht
      exact ⟨.pop a :: pre, post, by simp [canonicalEvents, ha, he]⟩
    · have ht : v = a ∨ v ∈ canonicalRecords (a+1) output := by
        simpa [canonicalRecords, ha] using hv
      rcases ht with hEq | ht
      · subst v
        have hs : next + (a-next) = a := by omega
        have hl : a+1-next = (a-next)+1 := by omega
        have he : List.range' next (a+1-next) = List.range' next (a-next) ++ [a] := by
          rw [hl, List.range'_concat]; simp [hs]
        exact ⟨(List.range' next (a-next)).map EndpointEvent.push,
          canonicalEvents (a+1) output, by simp [canonicalEvents, ha, he]⟩
      · obtain ⟨pre, post, he⟩ := ih ht
        exact ⟨(List.range' next (a+1-next)).map EndpointEvent.push ++ .pop a :: pre,
          post, by simp [canonicalEvents, ha, he, List.append_assoc]⟩

/-- Distinct event labels turn the consecutive event pair into consecutive
natural endpoint indices. -/
theorem canonical_record_consecutive {n v : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hv : v ∈ canonicalRecords 0 output) :
    (extractedEndpoints (canonicalEvents 0 output)).right v =
      (extractedEndpoints (canonicalEvents 0 output)).left v + 1 := by
  have hn := (permutation_canonical_validity hp).1
  obtain ⟨pre, post, he⟩ := canonical_record_adjacent hv
  rw [he] at hn ⊢
  have hd := (List.nodup_append.mp hn).2.2
  have hnp : EndpointEvent.push v ∉ pre := fun h => hd _ h _ (by simp) rfl
  have hno : EndpointEvent.pop v ∉ pre := fun h => hd _ h _ (by simp) rfl
  simp [extractedEndpoints, List.idxOf_append, List.idxOf_cons, hnp, hno, Nat.add_comm]

theorem canonical_record_vanishing {n v : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hv : v ∈ canonicalRecords 0 output) (t : Nat) :
    ¬ Covers (extractedEndpoints (canonicalEvents 0 output)) v t := by
  have he := canonical_record_consecutive hp hv
  unfold Covers
  omega

def nonrecordTokens (n : Nat) (output : List Nat) : Tokens :=
  (List.range n).filter (fun v => !(canonicalRecords 0 output).contains v)

/-- Removing records leaves every covering count of the canonical schedule
unchanged, including at endpoints nested within retained intervals. -/
theorem canonical_nonrecord_counts {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (t : Nat) :
    endpointCount (extractedEndpoints (canonicalEvents 0 output)) (nonrecordTokens n output) t =
      endpointCount (extractedEndpoints (canonicalEvents 0 output)) (List.range n) t := by
  apply endpointCount_filter_vanishing
  intro v _ hv
  have hm : v ∈ canonicalRecords 0 output := by simpa using hv
  exact canonical_record_vanishing hp hm

/-- Exact record-free recognition at positive widths, derived from the literal
machine's full canonical recognition iff and proved interval restoration. -/
theorem generated_iff_nonrecord_peelable {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s) :
    Run r s [] (List.range n) output [] ↔
      Peelable (extractedEndpoints (canonicalEvents 0 output)) r s (nonrecordTokens n output) := by
  apply (generated_iff_canonical_peelable hp).trans
  apply peelable_iff_filter_vanishing List.nodup_range hr hs
  intro v _ hv
  have hm : v ∈ canonicalRecords 0 output := by simpa using hv
  exact canonical_record_vanishing hp hm

#print axioms canonical_record_adjacent
#print axioms canonical_record_consecutive
#print axioms canonical_nonrecord_counts
#print axioms generated_iff_nonrecord_peelable
end StackSorting.Generalized

#print axioms StackSorting.IntervalCritical.Peelable.filter
#print axioms StackSorting.IntervalCritical.peelable_iff_filter_vanishing
