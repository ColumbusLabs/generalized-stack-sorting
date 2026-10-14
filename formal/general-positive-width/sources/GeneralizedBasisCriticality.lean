import GeneralizedEndpointDeletionTransport

/-! Literal one-deletion minimal rejection implies criticality of the canonical
nonrecord interval subsystem, and hence its global overlap bound. -/
namespace StackSorting.IntervalCritical
open List

theorem WellFormed.subset {e : Endpoints} {U V : Tokens}
    (h : WellFormed e U) (hn : V.Nodup) (hs : V ⊆ U) : WellFormed e V where
  nodup := hn
  proper v hv := h.proper v (hs hv)
  left_unique u hu v hv := h.left_unique u (hs hu) v (hs hv)
  right_unique u hu v hv := h.right_unique u (hs hu) v (hs hv)
  cross_distinct u hu v hv := h.cross_distinct u (hs hu) v (hs hv)

end StackSorting.IntervalCritical
namespace StackSorting.Generalized
open List IntervalCritical

/-- Every standardized nonrecord deletion is recognized exactly by erasing that
one interval from the original nonrecord subsystem, with original timestamps. -/
theorem nonrecord_deletion_generated_iff {r s n v : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hv : v ∈ nonrecordTokens n output) :
    Run r s [] (List.range (n-1)) (deleteWord v output) [] ↔
      Peelable (extractedEndpoints (canonicalEvents 0 output)) r s
        ((nonrecordTokens n output).erase v) := by
  have hparts := List.mem_filter.mp hv
  have hvr : v ∈ List.range n := hparts.1
  have hnon : v ∉ canonicalRecords 0 output := by simpa using hparts.2
  obtain ⟨hpd, _, hevents, _, htokens⟩ := permutation_nonrecord_deletion hp hvr hnon
  have hn : (nonrecordTokens n output).Nodup := List.nodup_range.filter _
  have hword : deleteWord v (nonrecordTokens n output) =
      ((nonrecordTokens n output).erase v).map (deleteRank v) := deleteWord_eq_erase_map hn
  have hrec := generated_iff_nonrecord_peelable hpd hr hs
  rw [hevents, htokens, hword] at hrec
  apply hrec.trans
  apply peelable_deleteEvents_map_iff
  intro u hu
  have hun : u ≠ v := by
    rw [hn.erase_eq_filter v] at hu
    simpa using (List.mem_filter.mp hu).2
  have huU := List.mem_of_mem_erase hu
  have hur : u ∈ List.range n := (List.mem_filter.mp huU).1
  obtain ⟨ops, ht, hi⟩ := permutation_canonical_trace hp
  have hup : u ∈ Generalized.inputs ops := by simpa [hi] using hur
  exact ⟨hun, ht.complete_event_members hup⟩

/-- Ordinary one-value deletion minimality, stated entirely in the existing
literal machine, implies interval Critical on the canonical nonrecords.
No interval-criticality, no-eligible, or width hypothesis is assumed. -/
theorem oneDeletionMinimal_nonrecord_critical {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] (List.range n) output [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (List.range (n-1)) (deleteWord v output) []) :
    Critical (extractedEndpoints (canonicalEvents 0 output)) r s (nonrecordTokens n output) := by
  constructor
  · intro h
    exact hreject ((generated_iff_nonrecord_peelable hp hr hs).mpr h)
  · intro v hv
    exact (nonrecord_deletion_generated_iff hp hr hs hv).mp
      (hdelete v (List.mem_filter.mp hv).1)

/-- The checked finite interval theorem now applies to an actual permutation
that is rejected but every standardized one-value deletion is generated. -/
theorem oneDeletionMinimal_nonrecord_overlap_le {r s n : Nat} {output : List Nat}
    (hp : output.Perm (List.range n)) (hr : 0 < r) (hs : 0 < s)
    (hreject : ¬ Run r s [] (List.range n) output [])
    (hdelete : ∀ v ∈ List.range n,
      Run r s [] (List.range (n-1)) (deleteWord v output) []) (cut : Nat) :
    overlap (extractedEndpoints (canonicalEvents 0 output)) (nonrecordTokens n output) cut ≤
      2 * max r s := by
  have hw := (permutation_canonical_validity hp).2.2.2.1
  have hsub : nonrecordTokens n output ⊆ List.range n := fun _ h => (List.mem_filter.mp h).1
  exact critical_overlap_le (hw.subset (List.nodup_range.filter _) hsub) hr hs
    (oneDeletionMinimal_nonrecord_critical hp hr hs hreject hdelete) cut

#print axioms nonrecord_deletion_generated_iff
#print axioms oneDeletionMinimal_nonrecord_critical
#print axioms oneDeletionMinimal_nonrecord_overlap_le
end StackSorting.Generalized
