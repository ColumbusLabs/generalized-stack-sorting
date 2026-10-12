import CapacityComplete
import CapacityAlgebra

/-! Instantiation with actual finite bounded-grammar cardinalities. -/
namespace StackSorting.Capacity
open StackSorting FirstReturn Mark PowerSeries FirstReturnAlgebra

noncomputable def enabledMatrix (h : Nat) (b : Mark) : Mat2 (PowerSeries ℤ) :=
  ⟨series h L (some b) true (some L), series h L (some b) true (some R),
   series h R (some b) true (some L), series h R (some b) true (some R)⟩

noncomputable def pushReturnMatrix (h : Nat) : Mat2 (PowerSeries ℤ) :=
  ⟨2 * X * series h R (some L) false (some L),
   2 * X * series h R (some L) false (some R),
   X * (series h R (some R) false (some L) + series h R (some L) false (some L)),
   X * (series h R (some R) false (some R) + series h R (some L) false (some R))⟩

theorem actual_recurs (h : Nat) (b d : Option Mark) :
    Recurs (pushReturnMatrix h) (C (count (h+1) 0 L b true d : ℤ))
      (C (count (h+1) 0 R b true d : ℤ))
      (series (h+1) L b true d) (series (h+1) R b true d) := by
  have hl := series_equation h L b d true
  have hr := series_equation h R b d true
  simp only [sum_mark] at hl hr
  constructor
  · dsimp [pushReturnMatrix]
    linear_combination hl
  · dsimp [pushReturnMatrix]
    linear_combination hr

noncomputable def actualIdentities : CapacityAlgebra.Identities ℤ where
  left h := enabledMatrix h L
  right h := enabledMatrix h R
  v := pushReturnMatrix
  bottomL h := series h L none true none
  bottomR h := series h R none true none
  complete := pathSeries
  left_zero := by simp [enabledMatrix, series_no_space, count_zero, eval]
  right_zero := by simp [enabledMatrix, series_no_space, count_zero, eval]
  bottomL_zero := by simp [series_no_space, count_zero, eval]
  complete_zero := pathSeries_no_space
  left_colL h := by
    simpa [enabledMatrix, count_zero, eval] using actual_recurs h (some L) (some L)
  left_colR h := by
    simpa [enabledMatrix, count_zero, eval] using actual_recurs h (some L) (some R)
  right_colL h := by
    simpa [enabledMatrix, count_zero, eval] using actual_recurs h (some R) (some L)
  right_colR h := by
    simpa [enabledMatrix, count_zero, eval] using actual_recurs h (some R) (some R)
  bottom h := by
    simpa [count_zero, eval] using actual_recurs h none none
  vll h := by
    have he := enabled_eq h R (some L) (some L)
    simp [count_zero, eval] at he
    dsimp [pushReturnMatrix, enabledMatrix]
    linear_combination -2 * (X : PowerSeries ℤ) * he
  vlr h := by
    have he := enabled_eq h R (some L) (some R)
    simp [count_zero, eval] at he
    dsimp [pushReturnMatrix, enabledMatrix]
    rw [he]
  vrl h := by
    have h₁ := enabled_eq h R (some R) (some L)
    have h₂ := enabled_eq h R (some L) (some L)
    simp [count_zero, eval] at h₁ h₂
    dsimp [pushReturnMatrix, enabledMatrix]
    linear_combination -(X : PowerSeries ℤ) * h₁ - (X : PowerSeries ℤ) * h₂
  vrr h := by
    have h₁ := enabled_eq h R (some R) (some R)
    have h₂ := enabled_eq h R (some L) (some R)
    simp [count_zero, eval] at h₁ h₂
    dsimp [pushReturnMatrix, enabledMatrix]
    linear_combination -(X : PowerSeries ℤ) * h₁ - (X : PowerSeries ℤ) * h₂
  empty_step h := by
    have he := enabled_eq h L none none
    simp [count_zero, eval] at he
    linear_combination pathSeries_equation h - (X : PowerSeries ℤ) * pathSeries (h+1) * he

/-- The auxiliary scalar k_H also counts a concrete bounded first-return family. -/
noncomputable def auxiliarySeries (h : Nat) : PowerSeries ℤ := series h L (some R) true (some L)

theorem auxiliarySeries_zero : auxiliarySeries 0 = 1 := by
  simp [auxiliarySeries, series_no_space, count_zero, eval]

/-- Uniform first-return recurrences for actual bounded labelled paths. -/
theorem actual_recurrence (h : Nat) :
    (1+X-4*X*auxiliarySeries h+2*X*pathSeries h)*auxiliarySeries (h+1) = 1 ∧
    (1-X*auxiliarySeries h)*pathSeries (h+1) = 1 := by
  exact CapacityAlgebra.recurrence actualIdentities h

theorem actual_recurrence_unique (k f : Nat → PowerSeries ℤ)
    (hk0 : k 0 = 1) (hf0 : f 0 = 1)
    (hk : ∀ h, (1+X-4*X*k h+2*X*f h)*k (h+1)=1)
    (hf : ∀ h, (1-X*k h)*f (h+1)=1) :
    ∀ h, k h = auxiliarySeries h ∧ f h = pathSeries h := by
  apply CapacityAlgebra.recurrence_unique k f auxiliarySeries pathSeries
  · exact hk0.trans auxiliarySeries_zero.symm
  · exact hf0.trans pathSeries_no_space.symm
  · exact hk
  · exact hf
  · exact fun h => (actual_recurrence h).1
  · exact fun h => (actual_recurrence h).2

#print axioms actualIdentities
#print axioms actual_recurrence
#print axioms actual_recurrence_unique
end StackSorting.Capacity
