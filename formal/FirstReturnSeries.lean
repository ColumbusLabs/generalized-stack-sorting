import GrammarCounting

namespace StackSorting.FirstReturn
open StackSorting Mark Op PowerSeries

@[simp] theorem coeff_series (n : Nat) (a : Mark) (b d : Option Mark) (flag : Bool) :
    coeff n (series a b flag d) = (count n a b flag d : ℤ) := by
  simp [series]

/-- The first-return equations are consequences of the proved finite grammar
bijection and its exact cardinalities, not hypotheses on a guessed series. -/
theorem series_equation (a : Mark) (b d : Option Mark) (flag : Bool) :
    series a b flag d = C (count 0 a b flag d : ℤ) +
      X * series a b true d +
      X * (∑ e : Mark, series R (some a) false (some e) * series e b true d) +
      X * (∑ e : Mark, series R (some L) false (some e) * series e b true d) := by
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

@[simp] theorem count_zero_disabled (a : Mark) (b d : Option Mark) :
    count 0 a b false d = 0 := by simp [count_zero, eval]

/-- Enabling pops adds exactly the labelled immediate-pop alternatives. -/
theorem enabled_eq (a : Mark) (b d : Option Mark) :
    series a b true d = C (count 0 a b true d : ℤ) + series a b false d := by
  ext n
  cases n with
  | zero => simp only [map_add, coeff_series, coeff_C, ite_true, count_zero_disabled, Nat.cast_zero, add_zero]
  | succ n =>
      simp only [map_add, coeff_C, Nat.succ_ne_zero, ite_false, zero_add, coeff_series]
      rw [count_succ, count_succ]

theorem sum_mark {A : Type*} [AddCommMonoid A] (f : Mark → A) :
    ∑ e : Mark, f e = f L + f R := by
  change (∑ e ∈ ({L, R} : Finset Mark), f e) = _
  simp


#print axioms series_equation
end StackSorting.FirstReturn
