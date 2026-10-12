import CapacityCounting
import FirstReturnSeries

namespace StackSorting.Capacity
open StackSorting FirstReturn Mark Op PowerSeries

@[simp] theorem coeff_series (h n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    coeff n (series h a b flag d) = (count h n a b flag d : ℤ) := by simp [series]

theorem series_equation (h : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    series (h+1) a b flag d = C (count (h+1) 0 a b flag d : ℤ) +
      X * series (h+1) a b true d +
      X * (∑ e : Mark, series h R (some a) false (some e) * series (h+1) e b true d) +
      X * (∑ e : Mark, series h R (some L) false (some e) * series (h+1) e b true d) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      simp only [map_add, coeff_succ_X_mul]
      simp only [coeff_C, Nat.succ_ne_zero, ite_false,
        zero_add, map_sum, coeff_mul, coeff_series]
      rw [count_succ]
      simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul]
      rw [Finset.sum_comm, Finset.sum_comm (s := Finset.antidiagonal n)]

@[simp] theorem count_zero_disabled (h : Nat) (a : Mark) (b d : Option Mark) :
    count h 0 a b false d = 0 := by simp [count_zero, eval]

theorem enabled_eq (h : Nat) (a : Mark) (b d : Option Mark) :
    series h a b true d = C (count h 0 a b true d : ℤ) + series h a b false d := by
  ext n
  cases n with
  | zero => simp only [map_add, coeff_series, coeff_C, ite_true, count_zero_disabled, Nat.cast_zero, add_zero]
  | succ n =>
      simp only [map_add, coeff_C, Nat.succ_ne_zero, ite_false, zero_add, coeff_series]
      cases h with
      | zero => simp [count_no_space]
      | succ h => rw [count_succ, count_succ]

theorem series_no_space (a : Mark) (b d : Option Mark) (flag : Bool) :
    series 0 a b flag d = C (count 0 0 a b flag d : ℤ) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp only [coeff_series, coeff_C, Nat.succ_ne_zero, ite_false, count_no_space, Nat.cast_zero]

@[simp] theorem constantCoeff_series (h : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    constantCoeff (series h a b flag d) = (count h 0 a b flag d : ℤ) := by
  rw [← coeff_zero_eq_constantCoeff]
  exact coeff_series h 0 a b d flag

#print axioms series_equation
#print axioms series_no_space
end StackSorting.Capacity
