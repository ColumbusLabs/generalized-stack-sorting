import GeneralizedInitialSchedule
import GeneralizedCoordinateRanks

/-! Restricting a global order to its old labels preserves their literal
maximum-insertion coordinates. Future labels are all larger, so they neither
end an old token's prefix nor contribute to its smaller-label rank. -/
namespace StackSorting.Generalized
namespace Coordinates

/-- Removing only labels strictly larger than the target leaves its exact
first-occurrence smaller-label rank unchanged. No distinctness is needed. -/
theorem rankSlot_filter (physical : List Nat) (p : Nat → Bool) (v : Nat)
    (hkeep : ∀ u ∈ physical, u ≤ v → p u) :
    rankSlot (physical.filter p) v = rankSlot physical v := by
  induction physical with
  | nil => simp [rankSlot]
  | cons head physical ih =>
    have ht : ∀ u ∈ physical, u ≤ v → p u :=
      fun u hu hv => hkeep u (by simp [hu]) hv
    by_cases he : head = v
    · subst head
      have hp := hkeep v (by simp) (Nat.le_refl v)
      simp [hp, rankSlot]
    · by_cases hp : p head
      · simp [hp, rankSlot, he, ih ht]
      · have hlarge : ¬ head < v := by
          intro hlt
          exact hp (hkeep head (by simp) (Nat.le_of_lt hlt))
        simp [hp, rankSlot, he, hlarge, ih ht]

end Coordinates
namespace InitialSchedule
open Coordinates

/-- The old-label projection contains each original old token exactly once. -/
theorem project_old_permutation {h n : Nat} {order : List Nat}
    (hp : order.Perm (List.range' 1 (h+n))) :
    (project order (List.range' 1 h)).Perm (List.range' 1 h) := by
  have hn := hp.nodup_iff.mpr List.nodup_range'
  apply (List.perm_ext_iff_of_nodup (hn.filter _) List.nodup_range').mpr
  intro v
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun hv => hv.2
  · intro hv
    refine ⟨hp.mem_iff.mpr ?_, hv⟩
    simp only [List.mem_range'_1] at hv ⊢
    omega

/-- Every old coordinate may be read directly from the full global order. -/
theorem rankSlot_project_old {h n v : Nat} {order : List Nat}
    (hp : order.Perm (List.range' 1 (h+n))) (hv : v ∈ List.range' 1 h) :
    rankSlot (project order (List.range' 1 h)) v = rankSlot order v := by
  apply rankSlot_filter
  intro u hu huv
  have hu' := hp.mem_iff.mp hu
  simp only [decide_eq_true_eq, List.mem_range'_1] at hu' hv ⊢
  omega

theorem rankWord_project_old {h n : Nat} {order : List Nat}
    (hp : order.Perm (List.range' 1 (h+n))) :
    rankWord (project order (List.range' 1 h)) 1 h = rankWord order 1 h := by
  apply List.map_congr_left
  intro v hv
  exact rankSlot_project_old hp hv

/-- Literal old-factor semantics can be tested against the full global order's
rank word; no old token is affected by the larger future labels. -/
theorem represents_project_iff {state : Decorated.State} {n : Nat} {order : List Nat}
    (hp : order.Perm (List.range' 1 (Decorated.height state + n))) :
    Decorated.Represents state (project order (List.range' 1 (Decorated.height state))) ↔
      Decorated.denotes state (rankWord order 1 (Decorated.height state)) := by
  rw [represents_iff_rankWord, rankWord_project_old hp]
  exact and_iff_right (project_old_permutation hp)

#print axioms project_old_permutation
#print axioms rankSlot_project_old
#print axioms represents_project_iff
end InitialSchedule
end StackSorting.Generalized
