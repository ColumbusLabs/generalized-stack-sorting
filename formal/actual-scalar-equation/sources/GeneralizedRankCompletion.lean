import InitialOrderProjection
import GeneralizedCompletionOrder
import GeneralizedUnaryBounds

/-! Composition theorem for an explicitly proved old-state rank description.
Concrete applications must supply the literal Represents equivalence below;
this module itself asserts no state-language identity or clause intersection. -/
namespace StackSorting.Generalized.Decorated
open Coordinates InitialSchedule StackSorting.MonotoneElimination

theorem rankBounds_project_iff {h n : Nat} {order : List Nat}
    {bounds : List (Nat × Nat)} (hp : order.Perm (List.range' 1 (h+n)))
    (hlabels : ∀ label bound, (label, bound) ∈ bounds → label ∈ List.range' 1 h) :
    RankBounds bounds (project order (List.range' 1 h)) ↔ RankBounds bounds order := by
  constructor
  · intro hb label bound hm
    rw [← rankSlot_project_old hp (hlabels label bound hm)]
    exact hb label bound hm
  · intro hb label bound hm
    rw [rankSlot_project_old hp (hlabels label bound hm)]
    exact hb label bound hm

/-- Static order recognition for any concrete old state whose represented
physical orders have the supplied, separately proved rank-bound description. -/
theorem completion_iff_rank_order (state : State) (n : Nat) (output : List Nat)
    (bounds : List (Nat × Nat))
    (hlabels : ∀ label bound, (label, bound) ∈ bounds →
      label ∈ List.range' 1 (height state))
    (hrep : ∀ physical, physical.Perm (List.range' 1 (height state)) →
      (Represents state physical ↔ RankBounds bounds physical)) :
    Completion state n output ↔
      traceInputs (canonicalEvents (height state + 1) output) =
        List.range' (height state + 1) n ∧
      traceOutputs (canonicalEvents (height state + 1) output) = output ∧
      InitialSchedule.Valid (List.range' 1 (height state))
        (canonicalEvents (height state + 1) output) ∧
      ∃ order, order.Perm (List.range' 1 (height state + n)) ∧
        FeasibleOrder (fun U v => BoundEligible bounds U v ∧
          ScheduleEligible 3 3 U v (List.range' 1 (height state))
            (canonicalEvents (height state + 1) output)) order := by
  have label_mem {order : List Nat} (hp : order.Perm (List.range' 1 (height state+n))) :
      ∀ label bound, (label, bound) ∈ bounds → label ∈ order := by
    intro label bound hm
    apply hp.mem_iff.mpr
    have hh := hlabels label bound hm
    simp only [List.mem_range'_1] at hh ⊢
    omega
  constructor
  · intro h
    obtain ⟨hi, ho, hv, order, hp, hr, hf⟩ :=
      (completion_iff_canonical_order state n output).mp h
    have hproj := project_old_permutation hp
    have hb := (rankBounds_project_iff hp hlabels).mp
      ((hrep _ hproj).mp hr)
    have hbound := (rankBounds_iff_feasible (hp.nodup_iff.mpr List.nodup_range')
      (label_mem hp)).mp hb
    refine ⟨hi, ho, hv, order, hp, ?_⟩
    apply (feasibleOrder_iff_prefixes _ order).mpr
    intro above v below he
    exact ⟨(feasibleOrder_iff_prefixes _ order).mp hbound above v below he,
      hf above v below he⟩
  · rintro ⟨hi, ho, hv, order, hp, hf⟩
    have hprefix := (feasibleOrder_iff_prefixes _ order).mp hf
    have hbound : FeasibleOrder (BoundEligible bounds) order :=
      (feasibleOrder_iff_prefixes _ order).mpr
        (fun above v below he => (hprefix above v below he).1)
    have hb := (rankBounds_iff_feasible (hp.nodup_iff.mpr List.nodup_range')
      (label_mem hp)).mpr hbound
    have hr := (hrep _ (project_old_permutation hp)).mpr
      ((rankBounds_project_iff hp hlabels).mpr hb)
    exact (completion_iff_canonical_order state n output).mpr
      ⟨hi, ho, hv, order, hp, hr, fun above v below he => (hprefix above v below he).2⟩

#print axioms rankBounds_project_iff
#print axioms completion_iff_rank_order
end StackSorting.Generalized.Decorated
