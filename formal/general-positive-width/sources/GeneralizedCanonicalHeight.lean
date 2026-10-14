import GeneralizedBasisCriticality

/-! The full canonical lazy stack height bound, including the transient physical
record token. The permutation orientation is increasing input, generated output. -/
namespace StackSorting.Generalized
open List IntervalCritical

/-- Consecutive record endpoints still give a real active physical cut, but
unique insertion indices imply at most one record is active at any one cut. -/
theorem canonical_record_overlap_le_one {n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (cut : Nat) :
    overlap (extractedEndpoints (canonicalEvents 0 output))
      ((List.range n).filter (canonicalRecords 0 output).contains) cut ≤ 1 := by
  let e := extractedEndpoints (canonicalEvents 0 output)
  let A := ((List.range n).filter (canonicalRecords 0 output).contains).filter
    (fun v => decide (Active e v cut))
  have hn : A.Nodup := (List.nodup_range.filter _).filter _
  have hw := (permutation_canonical_validity hp).2.2.2.1
  have heq : ∀ a ∈ A, ∀ b ∈ A, a = b := by
    intro a ha b hb
    obtain ⟨har, haa⟩ := List.mem_filter.mp ha
    obtain ⟨hbr, hba⟩ := List.mem_filter.mp hb
    obtain ⟨han, ham⟩ := List.mem_filter.mp har
    obtain ⟨hbn, hbm⟩ := List.mem_filter.mp hbr
    have hac := canonical_record_consecutive hp (List.contains_iff_mem.mp ham)
    have hbc := canonical_record_consecutive hp (List.contains_iff_mem.mp hbm)
    have hact : Active e a cut := by simpa using haa
    have hbct : Active e b cut := by simpa using hba
    have hleft : e.left a = e.left b := by
      change e.right a = e.left a + 1 at hac
      change e.right b = e.left b + 1 at hbc
      unfold Active at hact hbct
      omega
    exact hw.left_unique a han b hbn hleft
  have hlen : A.length ≤ 1 := by
    by_cases hz : A = []
    · simp [hz]
    · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil A hz
      have hsub : A ⊆ [a] := fun b hb => by simp [heq b hb a ha]
      simpa using hn.length_le_of_subset hsub
  simpa only [overlap, List.countP_eq_length_filter] using hlen

/-- Complete canonical overlap, now including records, for a literal
one-deletion-minimal rejected output permutation. -/
theorem oneDeletionMinimal_canonical_overlap_le {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] (List.range n) output [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (List.range (n-1)) (deleteWord v output) []) (cut : Nat) :
    overlap (extractedEndpoints (canonicalEvents 0 output)) (List.range n) cut ≤ 2 * max r s + 1 := by
  have hrecord := canonical_record_overlap_le_one hp cut
  have hnonrecord := oneDeletionMinimal_nonrecord_overlap_le hp hr hs hreject hdelete cut
  have hsplit := List.countP_eq_countP_filter_add (List.range n)
    (fun v => decide (Active (extractedEndpoints (canonicalEvents 0 output)) v cut))
    (canonicalRecords 0 output).contains
  change overlap (extractedEndpoints (canonicalEvents 0 output)) (List.range n) cut =
    overlap (extractedEndpoints (canonicalEvents 0 output))
      ((List.range n).filter (canonicalRecords 0 output).contains) cut +
    overlap (extractedEndpoints (canonicalEvents 0 output)) (nonrecordTokens n output) cut at hsplit
  omega

/-- Every actual post-event prefix stack length is exactly the overlap at the
corresponding physical cut, using the unchanged raw prefix and event indices. -/
theorem ExactTrace.prefix_length_eq_overlap {p q cut : Nat} {ops : List RawOp}
    {events : List EndpointEvent} {output middle emitted : List Nat}
    (ht : ExactTrace p q ops [] events [] output) (hin : (Generalized.inputs ops).Nodup)
    (hp : Generalized.run p q (ops.take (cut+1)) [] = some (middle, emitted)) :
    middle.length = overlap (extractedEndpoints events) (Generalized.inputs ops) cut := by
  obtain ⟨order, hn, _, hall⟩ := run_global_order_all_prefixes ht.run (by simpa using hin)
  have hsub := hall (ops.take (cut+1)) (ops.drop (cut+1))
    (List.take_append_drop (cut+1) ops).symm middle emitted hp
  have hmid : middle.Nodup := hn.sublist hsub
  have hmem : ∀ v, v ∈ middle ↔ v ∈ (Generalized.inputs ops).filter
      (fun v => decide (Active (extractedEndpoints events) v cut)) := by
    intro v
    constructor
    · intro hv
      have hi := ht.prefix_held_mem_input hp hv
      have ha : (extractedEndpoints events).left v < cut+1 ∧ cut+1 ≤ (extractedEndpoints events).right v :=
        (ht.prefix_active (m := cut+1) hin hp hi).mp hv
      apply List.mem_filter.mpr
      refine ⟨hi, ?_⟩
      exact _root_.decide_eq_true (show Active (extractedEndpoints events) v cut from ⟨by omega, by omega⟩)
    · intro hv
      obtain ⟨hi, ha⟩ := List.mem_filter.mp hv
      apply (ht.prefix_active (m := cut+1) hin hp hi).mpr
      have hactive : Active (extractedEndpoints events) v cut := _root_.of_decide_eq_true ha
      obtain ⟨hl, hr⟩ := hactive
      exact ⟨by omega, by omega⟩
  have he := (List.perm_ext_iff_of_nodup hmid (hin.filter _)).mpr hmem
  simpa only [overlap, List.countP_eq_length_filter] using he.length_eq

/-- Any actual realization of the canonical event list has the same bounded
prefix heights, even though a rejected permutation needs permissive widths for
such a realization. The rejection widths are still the explicit `r,s`. -/
theorem oneDeletionMinimal_canonical_prefix_height_le {r s n p q m : Nat}
    {output middle emitted : List Nat} {ops : List RawOp}
    (hperm : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] (List.range n) output [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (List.range (n-1)) (deleteWord v output) [])
    (ht : ExactTrace p q ops [] (canonicalEvents 0 output) [] output)
    (hi : Generalized.inputs ops = List.range n)
    (hp : Generalized.run p q (ops.take m) [] = some (middle, emitted)) :
    middle.length ≤ 2 * max r s + 1 := by
  cases m with
  | zero =>
    have he : middle = [] := congrArg Prod.fst (Option.some.inj hp).symm
    simp [he]
  | succ cut =>
    have hn : (Generalized.inputs ops).Nodup := by simpa [hi] using (List.nodup_range (n := n))
    rw [ht.prefix_length_eq_overlap hn hp, hi]
    exact oneDeletionMinimal_canonical_overlap_le hperm hr hs hreject hdelete cut

/-- End-to-end literal lazy-height theorem. No history or interval certificate
is assumed: one exists with the exact canonical schedule and all prefix stacks,
including transient record states, bounded by `2*max r s+1`. -/
theorem oneDeletionMinimal_canonical_history_height_le {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] (List.range n) output [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (List.range (n-1)) (deleteWord v output) []) :
    ∃ ops, ExactTrace 1 (n+1) ops [] (canonicalEvents 0 output) [] output ∧
      Generalized.inputs ops = List.range n ∧
      ∀ m middle emitted,
        Generalized.run 1 (n+1) (ops.take m) [] = some (middle, emitted) →
        middle.length ≤ 2 * max r s + 1 := by
  obtain ⟨ops, ht, hi⟩ := permutation_canonical_trace hp
  exact ⟨ops, ht, hi, fun _ _ _ hprefix =>
    oneDeletionMinimal_canonical_prefix_height_le hp hr hs hreject hdelete ht hi hprefix⟩

#print axioms canonical_record_overlap_le_one
#print axioms oneDeletionMinimal_canonical_overlap_le
#print axioms ExactTrace.prefix_length_eq_overlap
#print axioms oneDeletionMinimal_canonical_prefix_height_le
#print axioms oneDeletionMinimal_canonical_history_height_le
end StackSorting.Generalized
