import CountingSemantics
import FirstReturnAlgebra

/-! # The generating function of original-machine-sortable permutations

This module instantiates the algebraic first-return identities with the actual
finite-cardinality series of the proved grammar/permutation bijection. The
final theorem has no supplied recurrence or counting-series hypothesis.
-/
namespace StackSorting.FirstReturn
open StackSorting Mark PowerSeries FirstReturnAlgebra

noncomputable def enabledMatrix (b : Mark) : Mat2 (PowerSeries ℤ) :=
  ⟨series L (some b) true (some L), series L (some b) true (some R),
   series R (some b) true (some L), series R (some b) true (some R)⟩

noncomputable def pushReturnMatrix : Mat2 (PowerSeries ℤ) :=
  ⟨2 * X * series R (some L) false (some L),
   2 * X * series R (some L) false (some R),
   X * (series R (some R) false (some L) + series R (some L) false (some L)),
   X * (series R (some R) false (some R) + series R (some L) false (some R))⟩

theorem actual_recurs (b d : Option Mark) :
    Recurs pushReturnMatrix (C (count 0 L b true d : ℤ)) (C (count 0 R b true d : ℤ))
      (series L b true d) (series R b true d) := by
  have hl := series_equation L b d true
  have hr := series_equation R b d true
  simp only [sum_mark] at hl hr
  constructor
  · dsimp [pushReturnMatrix]
    linear_combination hl
  · dsimp [pushReturnMatrix]
    linear_combination hr

/-- Every field is supplied by a previously proved finite-cardinality identity. -/
noncomputable def actualIdentities : Identities ℤ where
  left := enabledMatrix L
  right := enabledMatrix R
  v := pushReturnMatrix
  bottomL := series L none true none
  bottomR := series R none true none
  complete := pathSeries
  left_colL := by
    simpa [enabledMatrix, count_zero, eval] using actual_recurs (some L) (some L)
  left_colR := by
    simpa [enabledMatrix, count_zero, eval] using actual_recurs (some L) (some R)
  right_colL := by
    simpa [enabledMatrix, count_zero, eval] using actual_recurs (some R) (some L)
  right_colR := by
    simpa [enabledMatrix, count_zero, eval] using actual_recurs (some R) (some R)
  bottom := by
    simpa [count_zero, eval] using actual_recurs none none
  vll := by
    have h := enabled_eq R (some L) (some L)
    simp [count_zero, eval] at h
    dsimp [pushReturnMatrix, enabledMatrix]
    linear_combination -2 * (X : PowerSeries ℤ) * h
  vlr := by
    have h := enabled_eq R (some L) (some R)
    simp [count_zero, eval] at h
    dsimp [pushReturnMatrix, enabledMatrix]
    rw [h]
  vrl := by
    have h₁ := enabled_eq R (some R) (some L)
    have h₂ := enabled_eq R (some L) (some L)
    simp [count_zero, eval] at h₁ h₂
    dsimp [pushReturnMatrix, enabledMatrix]
    linear_combination -(X : PowerSeries ℤ) * h₁ - (X : PowerSeries ℤ) * h₂
  vrr := by
    have h₁ := enabled_eq R (some R) (some R)
    have h₂ := enabled_eq R (some L) (some R)
    simp [count_zero, eval] at h₁ h₂
    dsimp [pushReturnMatrix, enabledMatrix]
    linear_combination -(X : PowerSeries ℤ) * h₁ - (X : PowerSeries ℤ) * h₂
  empty_step := by
    have h := enabled_eq L none none
    simp [count_zero, eval] at h
    linear_combination pathSeries_equation - (X : PowerSeries ℤ) * pathSeries * h

/-- Coefficients are cardinalities of distinct inputs sortable by the original
single-token, top-two-position machine, with no bypass primitive. -/
theorem sortingSeries_coeff (n : Nat) :
    coeff n sortingSeries = (Fintype.card (SortableInput n) : ℤ) := by
  simp [sortingSeries]

theorem sortingSeries_constant : constantCoeff sortingSeries = 1 := by
  rw [sortingSeries_eq_pathSeries]
  exact constantCoeff_pathSeries

/-- The known cubic is derived from the original machine at all lengths. -/
theorem sortingSeries_cubic :
    2 * X * sortingSeries ^ 3 - (2 * X + 3) * sortingSeries ^ 2 +
      (7 - X) * sortingSeries - 4 = 0 := by
  rw [sortingSeries_eq_pathSeries]
  exact cubic actualIdentities

/-- The actual permutation series is the unique formal branch with constant1. -/
theorem sortingSeries_unique (f : PowerSeries ℤ)
    (h₀ : constantCoeff f = 1)
    (h : 2 * X * f ^ 3 - (2 * X + 3) * f ^ 2 + (7 - X) * f - 4 = 0) :
    f = sortingSeries :=
  cubic_branch_unique f sortingSeries h₀ sortingSeries_constant h sortingSeries_cubic

#print axioms actualIdentities
#print axioms sortingSeries_coeff
#print axioms sortingSeries_constant
#print axioms sortingSeries_cubic
#print axioms sortingSeries_unique
end StackSorting.FirstReturn
