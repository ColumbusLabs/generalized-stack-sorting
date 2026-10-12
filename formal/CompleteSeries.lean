import CompleteCounting
import FirstReturnSeries

namespace StackSorting.FirstReturn
open StackSorting Mark Op PowerSeries

@[simp] theorem coeff_pathSeries (n : Nat) :
    coeff n pathSeries = (pathCount n : ℤ) := by simp [pathSeries]

/-- The true empty-stack decomposition, with the disabled L completion and a
real bottom boundary, derived from the cardinality of complete grammar paths. -/
theorem pathSeries_equation :
    pathSeries = 1 + X * pathSeries + X * (series L none false none * pathSeries) := by
  ext n
  cases n with
  | zero => simp [pathCount_zero]
  | succ n =>
      simp only [map_add, coeff_succ_X_mul]
      simp only [coeff_one, Nat.succ_ne_zero, ite_false, zero_add,
        coeff_mul, coeff_series, coeff_pathSeries]
      rw [pathCount_succ]
      simp

@[simp] theorem constantCoeff_pathSeries : constantCoeff pathSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_pathSeries, pathCount_zero]
  rfl

@[simp] theorem constantCoeff_series (a : Mark) (b d : Option Mark) (flag : Bool) :
    constantCoeff (series a b flag d) = (count 0 a b flag d : ℤ) := by
  rw [← coeff_zero_eq_constantCoeff]
  exact coeff_series 0 a b d flag

#print axioms pathSeries_equation
end StackSorting.FirstReturn
