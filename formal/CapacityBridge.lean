import PhysicalCapacity
import CapacityHeight

/-! Exact adapter from bounded original sorting to the grammar's physical meter. -/
namespace StackSorting.Labelled
open TForest

theorem stackStep_height (act : Action) (s t : SState) (out : List Nat)
    (hs : stackStep act s = some (t,out)) :
    t.1.length = Capacity.nextHeight (eraseAction act) s.1.length ∧
      (IsPop act → 0 < s.1.length) := by
  rcases s with ⟨held,flag⟩
  cases act <;> cases held with
  | nil =>
    simp [stackStep] at hs
    all_goals rcases hs with ⟨rfl,rfl⟩
    all_goals simp [eraseAction, Capacity.nextHeight, IsPop]
  | cons a rest =>
    cases rest <;> cases flag <;> simp [stackStep] at hs
    all_goals rcases hs with ⟨rfl,rfl⟩
    all_goals simp [eraseAction, Capacity.nextHeight, IsPop]
    all_goals omega

theorem forestFits_iff_fits (H : Nat) (acts : List Action) (s t : TState)
    (out : List Nat) (hr : tokenRun acts s = some (t,out)) :
    ForestFits H acts s ↔ Capacity.Fits H (acts.map eraseAction) (tokens s.1).length := by
  induction acts generalizing s out with
  | nil => rfl
  | cons act acts ih =>
    obtain ⟨u, emitted, tail, hs, ht, _⟩ := split_run act acts s t out hr
    have hh := stackStep_height act (stackState s) (stackState u) emitted
      (stack_step act s u emitted hs)
    simp only [stackState] at hh
    simp only [ForestFits, hs, List.map_cons]
    rw [ih u tail ht, hh.1]
    cases act with
    | bypass a => simp [introduced, eraseAction, Capacity.nextHeight, Capacity.Fits]
    | push0 a =>
      simp only [introduced, ne_eq, List.cons_ne_self, not_false_eq_true, true_implies,
        eraseAction, Capacity.nextHeight, Capacity.Fits]
      exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,Capacity.fits_initial h.2,h.2⟩⟩
    | push1 a =>
      simp only [introduced, ne_eq, List.cons_ne_self, not_false_eq_true, true_implies,
        eraseAction, Capacity.nextHeight, Capacity.Fits]
      exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,Capacity.fits_initial h.2,h.2⟩⟩
    | pop0 =>
      have hp := hh.2 trivial
      simp [introduced, eraseAction, Capacity.nextHeight, Capacity.Fits, hp]
    | pop1 =>
      have hp := hh.2 trivial
      simp [introduced, eraseAction, Capacity.nextHeight, Capacity.Fits, hp]

/-- The finite-capacity word predicate counts true minimum-capacity permutations,
not just histories bounded under a possibly nonoptimal sorting strategy. -/
theorem canonical_capacity_iff_fits (H : Nat) (acts : List Action) (c : Bool) (n : Nat)
    (hr : tokenRun acts (nil,true) = some ((nil,c), List.range' 1 n)) :
    CanSortWithin H (inputs acts) n ↔ Capacity.Fits H (acts.map eraseAction) 0 := by
  rw [canonical_capacity_optimal H acts c n hr]
  exact (forestFits_iff_rawFits H acts (nil,true) (nil,c) _ hr).symm.trans
    (forestFits_iff_fits H acts (nil,true) (nil,c) _ hr)

#print axioms forestFits_iff_fits
#print axioms canonical_capacity_iff_fits
end StackSorting.Labelled
