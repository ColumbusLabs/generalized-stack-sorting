import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination

/-! # Formal algebra of the direct first-return equations

These are conditional algebraic theorems over the exact first-return equations.
The separate grammar/cardinality layer must establish those equations for the
actual counting series. No counts or coefficient agreements are assumed here.
-/
namespace StackSorting.FirstReturnAlgebra

structure Mat2 (A : Type*) where
  ll : A
  lr : A
  rl : A
  rr : A

variable {R : Type*} [CommRing R]
local notation "S" => PowerSeries R
local notation "x" => (PowerSeries.X : S)

def Recurs (v : Mat2 S) (d₀ d₁ y₀ y₁ : S) : Prop :=
  y₀ = d₀ + x * y₀ + v.ll * y₀ + v.lr * y₁ ∧
  y₁ = d₁ + x * y₁ + v.rl * y₀ + v.rr * y₁

theorem unit_one_sub_X_mul (a : S) : IsUnit (1 - x * a) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp

/-- A two-state first-return linear system is uniquely solvable whenever its
transition matrix has zero constant coefficient. Only uniqueness is needed. -/
theorem recurs_unique (v : Mat2 S)
    (hvll : PowerSeries.constantCoeff v.ll = 0)
    (hvlr : PowerSeries.constantCoeff v.lr = 0)
    (hvrl : PowerSeries.constantCoeff v.rl = 0)
    (hvrr : PowerSeries.constantCoeff v.rr = 0)
    (d₀ d₁ y₀ y₁ z₀ z₁ : S)
    (hy : Recurs v d₀ d₁ y₀ y₁) (hz : Recurs v d₀ d₁ z₀ z₁) :
    y₀ = z₀ ∧ y₁ = z₁ := by
  let a : S := 1 - x - v.ll
  let d : S := 1 - x - v.rr
  let det : S := a * d - v.lr * v.rl
  have hu : IsUnit det := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp [det, a, d, hvll, hvlr, hvrl, hvrr]
  have h₀ : det * (y₀ - z₀) = 0 := by
    dsimp [det, a, d]
    linear_combination (1 - x - v.rr) * hy.1 + v.lr * hy.2 -
      (1 - x - v.rr) * hz.1 - v.lr * hz.2
  have h₁ : det * (y₁ - z₁) = 0 := by
    dsimp [det, a, d]
    linear_combination v.rl * hy.1 + (1 - x - v.ll) * hy.2 -
      v.rl * hz.1 - (1 - x - v.ll) * hz.2
  exact ⟨sub_eq_zero.mp (hu.mul_left_cancel (by simpa using h₀)),
    sub_eq_zero.mp (hu.mul_left_cancel (by simpa using h₁))⟩

/-- The enabled nonbottom matrices, true-bottom column, and empty-path series
satisfy the actual first-step decompositions. Disabled series have already been
replaced by enabled series minus the immediate-pop constants. -/
structure Identities (R : Type*) [CommRing R] where
  left : Mat2 (PowerSeries R)
  right : Mat2 (PowerSeries R)
  v : Mat2 (PowerSeries R)
  bottomL : PowerSeries R
  bottomR : PowerSeries R
  complete : PowerSeries R
  left_colL : Recurs v 2 1 left.ll left.rl
  left_colR : Recurs v 0 0 left.lr left.rr
  right_colL : Recurs v 1 0 right.ll right.rl
  right_colR : Recurs v 1 1 right.lr right.rr
  bottom : Recurs v 1 1 bottomL bottomR
  vll : v.ll = 2 * PowerSeries.X * (left.rl - 1)
  vlr : v.lr = 2 * PowerSeries.X * left.rr
  vrl : v.rl = PowerSeries.X * (right.rl + left.rl - 1)
  vrr : v.rr = PowerSeries.X * (right.rr - 1 + left.rr)
  empty_step : complete = 1 + PowerSeries.X * complete +
    PowerSeries.X * (bottomL - 1) * complete

/-- The full two-state first-return identities reduce to two scalar series.
No division by X or selection using initial numerical coefficients is used. -/
theorem scalar_reduction (s : Identities R) :
    ∃ k : S, s.complete = 1 + x * k * s.complete ∧
      k = 1 + x * k * (4 * k - 2 * s.complete - 1) := by
  have hvll : PowerSeries.constantCoeff s.v.ll = 0 := by simp [s.vll]
  have hvlr : PowerSeries.constantCoeff s.v.lr = 0 := by simp [s.vlr]
  have hvrl : PowerSeries.constantCoeff s.v.rl = 0 := by simp [s.vrl]
  have hvrr : PowerSeries.constantCoeff s.v.rr = 0 := by simp [s.vrr]
  have uniq := recurs_unique s.v hvll hvlr hvrl hvrr
  have hz : s.left.lr = 0 ∧ s.left.rr = 0 :=
    uniq 0 0 _ _ 0 0 s.left_colR (by constructor <;> simp)
  have hsum : s.left.ll = s.right.ll + s.right.lr ∧
      s.left.rl = s.right.rl + s.right.rr := by
    apply uniq 2 1 _ _ _ _ s.left_colL
    constructor
    · linear_combination s.right_colL.1 + s.right_colR.1
    · linear_combination s.right_colL.2 + s.right_colR.2
  have hb : s.bottomL = s.right.lr ∧ s.bottomR = s.right.rr :=
    uniq 1 1 _ _ _ _ s.bottom s.right_colR
  have hvlr0 : s.v.lr = 0 := by simp [s.vlr, hz.2]
  have htopunit : IsUnit (1 - x - s.v.ll) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp [hvll]
  have htop : (1 - x - s.v.ll) * (s.right.ll - s.right.lr) = 0 := by
    have ha := s.right_colL.1
    have hb := s.right_colR.1
    rw [hvlr0] at ha hb
    linear_combination ha - hb
  have htopEq : s.right.ll = s.right.lr :=
    sub_eq_zero.mp (htopunit.mul_left_cancel (by simpa using htop))
  let k := s.right.ll
  let u := s.right.rl
  let j := s.right.rr
  have hv00 : s.v.ll = 2 * x * (u + j - 1) := by
    rw [s.vll, hsum.2]
  have hv10 : s.v.rl = x * (2 * u + j - 1) := by
    rw [s.vrl, hsum.2]
    dsimp [u, j]
    ring
  have hv11 : s.v.rr = x * (j - 1) := by simp [s.vrr, hz.2, j]
  have hk : k = 1 + x * k * (2 * u + 2 * j - 1) := by
    have h := s.right_colL.1
    rw [hvlr0, hv00] at h
    dsimp [k, u, j] at *
    linear_combination h
  have hj : j = 1 + x * j * j + x * (2 * u + j - 1) * k := by
    have h := s.right_colR.2
    rw [hv10, hv11, ← htopEq] at h
    dsimp [k, u, j] at *
    linear_combination h
  have hu : u = x * j * u + x * (2 * u + j - 1) * k := by
    have h := s.right_colL.2
    rw [hv10, hv11] at h
    dsimp [k, u, j] at *
    linear_combination h
  have hkj0 : (1 - x * j) * (k - j) = 0 := by
    linear_combination hk - hj
  have hkj : k = j := sub_eq_zero.mp
    ((unit_one_sub_X_mul j).mul_left_cancel (by simpa using hkj0))
  have hf : s.complete = 1 + x * k * s.complete := by
    have h := s.empty_step
    rw [hb.1, ← htopEq] at h
    dsimp [k]
    linear_combination h
  have hlf0 : (1 - x * k) * ((j - u) - s.complete) = 0 := by
    rw [hkj] at hf ⊢
    linear_combination hj - hu - hf
  have hlf : j - u = s.complete := sub_eq_zero.mp
    ((unit_one_sub_X_mul k).mul_left_cancel (by simpa using hlf0))
  refine ⟨k, hf, ?_⟩
  rw [← hkj] at hk hlf
  linear_combination hk - 2 * x * k * hlf

/-- Pure polynomial elimination of the two scalar first-return equations. -/
theorem scalar_cubic {A : Type*} [CommRing A] (z k f : A)
    (hf : f = 1 + z * k * f)
    (hk : k = 1 + z * k * (4 * k - 2 * f - 1)) :
    2 * z * f ^ 3 - (2 * z + 3) * f ^ 2 + (7 - z) * f - 4 = 0 := by
  linear_combination z * f ^ 2 * hk -
    (4 * z * k * f + 3 * f - 4 - 2 * z * f ^ 2 - z * f) * hf

/-- The cubic follows from the complete first-return equations. -/
theorem cubic (s : Identities R) :
    2 * x * s.complete ^ 3 - (2 * x + 3) * s.complete ^ 2 +
      (7 - x) * s.complete - 4 = 0 := by
  obtain ⟨k, hf, hk⟩ := scalar_reduction s
  exact scalar_cubic x k s.complete hf hk

/-- The branch with constant coefficient 1 is unique over every commutative
coefficient ring: the difference factor has unit constant coefficient 1. -/
theorem cubic_branch_unique (f g : S)
    (hf0 : PowerSeries.constantCoeff f = 1)
    (hg0 : PowerSeries.constantCoeff g = 1)
    (hf : 2 * x * f ^ 3 - (2 * x + 3) * f ^ 2 + (7 - x) * f - 4 = 0)
    (hg : 2 * x * g ^ 3 - (2 * x + 3) * g ^ 2 + (7 - x) * g - 4 = 0) :
    f = g := by
  let q := 2 * x * (f ^ 2 + f * g + g ^ 2) - (2 * x + 3) * (f + g) + (7 - x)
  have hq : IsUnit q := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    norm_num [q, hf0, hg0, map_ofNat]
  have he : q * (f - g) = 0 := by
    dsimp [q]
    linear_combination hf - hg
  exact sub_eq_zero.mp (hq.mul_left_cancel (by simpa using he))

theorem constantCoeff_complete (s : Identities R) :
    PowerSeries.constantCoeff s.complete = 1 := by
  have h := congrArg (PowerSeries.constantCoeff : S → R) s.empty_step
  simpa using h

/-- Any two complete first-return systems have the same empty-path series. -/
theorem complete_unique (s t : Identities R) : s.complete = t.complete :=
  cubic_branch_unique s.complete t.complete (constantCoeff_complete s)
    (constantCoeff_complete t) (cubic s) (cubic t)

#print axioms scalar_reduction
#print axioms cubic
#print axioms cubic_branch_unique
#print axioms constantCoeff_complete
#print axioms complete_unique
end StackSorting.FirstReturnAlgebra
