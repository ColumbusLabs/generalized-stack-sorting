import GeneralizedInitialSchedule
import GeneralizedDecoratedSemantics

/-! Literal decorated completion as a static total-order feasibility problem.
The old active labels are the fixed common rank set, independent of the
existential initial physical stack. -/
namespace StackSorting.Generalized
namespace Decorated
open InitialSchedule

/-- The complete physical input supply is duplicate-free. -/
theorem Represents.supply_nodup {state : State} {physical : List Nat}
    (h : Represents state physical) (n : Nat) :
    (physical ++ List.range' (height state + 1) n).Nodup := by
  have hp := h.permutation.append_right (List.range' (height state + 1) n)
  have hr : List.range' 1 (height state) ++ List.range' (height state + 1) n =
      List.range' 1 (height state + n) := by simp [Nat.add_comm]
  rw [hr] at hp
  exact hp.nodup_iff.mpr List.nodup_range'

theorem Represents.old_bounds {state : State} {physical : List Nat}
    (h : Represents state physical) : ∀ v ∈ physical, v < height state + 1 := by
  intro v hv
  have ht := List.mem_range'.mp (h.permutation.mem_iff.mp hv)
  omega

/-- No count quotient or intersection identity is assumed. This is a direct
bidirectional bridge from the existing physical Completion definition to a
single global order with old-factor semantics and literal future event bounds. -/
theorem completion_iff_canonical_order (state : State) (n : Nat) (output : List Nat) :
    Completion state n output ↔
      traceInputs (canonicalEvents (height state + 1) output) =
        List.range' (height state + 1) n ∧
      traceOutputs (canonicalEvents (height state + 1) output) = output ∧
      InitialSchedule.Valid (List.range' 1 (height state))
        (canonicalEvents (height state + 1) output) ∧
      ∃ order, order.Perm (List.range' 1 (height state + n)) ∧
        Represents state (project order (List.range' 1 (height state))) ∧
        Feasible 3 3 order (List.range' 1 (height state))
          (canonicalEvents (height state + 1) output) := by
  constructor
  · rintro ⟨physical, hrep, hrun⟩
    obtain ⟨hi, ho, hv, order, hp, hinit, hf⟩ :=
      (run_iff_canonical_order (hrep.supply_nodup n) hrep.old_bounds).mp hrun
    have hold := hrep.permutation
    have hsource := hp.trans (hold.append_right (List.range' (height state + 1) n))
    have hr : List.range' 1 (height state) ++ List.range' (height state + 1) n =
        List.range' 1 (height state + n) := by simp [Nat.add_comm]
    rw [hr] at hsource
    refine ⟨hi, ho, hv.perm hold, order, hsource, ?_, hf.pool_perm hold⟩
    rw [← project_pool_perm hold, hinit]
    exact hrep
  · rintro ⟨hi, ho, hv, order, hp, hrep, hf⟩
    refine ⟨project order (List.range' 1 (height state)), hrep, ?_⟩
    have hn := hp.nodup_iff.mpr List.nodup_range'
    have hr : List.range' 1 (height state) ++ List.range' (height state + 1) n =
        List.range' 1 (height state + n) := by simp [Nat.add_comm]
    have hsub : List.range' 1 (height state) ⊆ order := by
      intro v hv
      apply hp.mem_iff.mpr
      rw [← hr]
      exact List.mem_append_left _ hv
    have hinput : traceInputs (canonicalEvents (height state + 1) output) ⊆ order := by
      intro v hv
      apply hp.mem_iff.mpr
      rw [← hr]
      rw [hi] at hv
      exact List.mem_append_right _ hv
    simpa [hi, ho] using feasible_history hn List.nodup_range' hsub hinput hv hf

#print axioms completion_iff_canonical_order
end Decorated
end StackSorting.Generalized
