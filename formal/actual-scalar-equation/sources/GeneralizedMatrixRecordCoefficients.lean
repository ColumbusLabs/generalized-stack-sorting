import FormalResolvent

/-! Coefficientwise finite record-batch expansion of a genuine formal matrix
resolvent. No infinite-sum axiom or bounded-prefix extrapolation is used. -/
namespace StackSorting.FiniteGraph
namespace RecordCoefficients
open StackSorting.CauchyRing StackSorting.ProperSeries

noncomputable def readRow (T : Mat FPS 6 6) (row : Vec FPS 6) : Nat → Vec FPS 6
  | 0 => row
  | count+1 => readRow T (vm row T) count

noncomputable def recordCoeff (T : Mat FPS 6 6) (beta row : Vec FPS 6) : Nat → Rat
  | 0 => 0
  | count+1 => dot row beta count + recordCoeff T beta (vm row T) count

theorem dot_scale_right (row col : Vec FPS 6) (s : FPS) :
    dot row (fun i => s*col i) = s*dot row col := by
  unfold dot
  rw [←mul_sumFin]
  apply sumFin_congr
  intro i
  grind

theorem record_row_equation (T : Mat FPS 6 6) (beta gamma row : Vec FPS 6)
    (hgamma : ∀ i, gamma i = beta i+X*mv T gamma i) :
    dot row gamma = dot row beta + X*dot (vm row T) gamma := by
  calc
    dot row gamma = dot row (fun i => beta i+X*mv T gamma i) :=
      congrArg (dot row) (funext hgamma)
    _ = dot row beta + dot row (fun i => X*mv T gamma i) := dot_add _ _ _
    _ = dot row beta + X*dot row (mv T gamma) := by rw [dot_scale_right]
    _ = dot row beta + X*dot (vm row T) gamma := by rw [dot_vm]

theorem X_coeff_zero (a : FPS) : (X*a) 0 = 0 := congrFun (X_mul_coeff a) 0

theorem X_coeff_succ (a : FPS) (n : Nat) : (X*a) (n+1) = a n :=
  congrFun (X_mul_coeff a) (n+1)

/-- The record contribution at size n is determined by exactly the first n
iterations, because each additional record batch brings one factor X. -/
theorem record_coeff_eq (T : Mat FPS 6 6) (beta gamma : Vec FPS 6)
    (hgamma : ∀ i, gamma i = beta i+X*mv T gamma i) (row : Vec FPS 6) (n : Nat) :
    (X*dot row gamma) n = recordCoeff T beta row n := by
  induction n generalizing row with
  | zero => exact X_coeff_zero _
  | succ n ih =>
    rw [X_coeff_succ]
    have he := congrArg (fun f : FPS => f n) (record_row_equation T beta gamma row hgamma)
    change dot row gamma n = dot row beta n + (X*dot (vm row T) gamma) n at he
    rw [ih] at he
    exact he

/-- Exact finite batch indexing, b=1,...,n, including the b-1 held appends. -/
theorem recordCoeff_eq_sum (T : Mat FPS 6 6) (beta row : Vec FPS 6) (n : Nat) :
    recordCoeff T beta row n =
      ((List.range' 1 n).map (fun batch => dot (readRow T row (batch-1)) beta (n-batch))).sum := by
  induction n generalizing row with
  | zero => rfl
  | succ n ih =>
    simp only [recordCoeff, List.range'_succ, List.map_cons, List.sum_cons,
      Nat.add_sub_cancel, Nat.sub_self, readRow]
    rw [ih]
    congr 1
    rw [List.range'_succ_left (s := 1), List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro batch hb
    have hpositive := (List.mem_range'_1.mp hb).1
    cases batch with
    | zero => omega
    | succ batch => simp [readRow, Nat.add_sub_add_right]

#print axioms record_coeff_eq
#print axioms recordCoeff_eq_sum
end RecordCoefficients
end StackSorting.FiniteGraph
