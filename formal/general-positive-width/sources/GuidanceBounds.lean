import Mathlib.Tactic

namespace StackSorting.GuidedPathwidth

/-- Deliberately coarse palette budget for the forthcoming genuine forest
induction. Defining this budget alone is not a guidance-existence theorem. -/
def paletteBound (k : Nat) : Nat → Nat
  | 0 => k
  | h+1 => 12*k + 2^(4*k+1) * paletteBound k h

theorem paletteBound_step (k h : Nat) : paletteBound k h ≤ paletteBound k (h+1) := by
  have hp : 1 ≤ (2:Nat)^(4*k+1) := by
    have hpos : 0 < (2:Nat)^(4*k+1) := by positivity
    omega
  have hh := Nat.mul_le_mul_right (paletteBound k h) hp
  change paletteBound k h ≤ 12*k + 2^(4*k+1) * paletteBound k h
  simp only [Nat.one_mul] at hh
  omega

theorem paletteBound_mono (k : Nat) : Monotone (paletteBound k) := by
  exact monotone_nat_of_le_succ (paletteBound_step k)

theorem binaryCost_le_step (k h : Nat) :
    2^k * paletteBound k h + 2*k ≤ paletteBound k (h+1) := by
  have hp : (2:Nat)^k ≤ 2^(4*k+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hm := Nat.mul_le_mul_right (paletteBound k h) hp
  change 2^k * paletteBound k h + 2*k ≤ 12*k + 2^(4*k+1)*paletteBound k h
  omega

theorem idempotentCost_le_step (k h : Nat) :
    2^(3*k) * paletteBound k h + 9*k ≤ paletteBound k (h+1) := by
  have hp : (2:Nat)^(3*k) ≤ 2^(4*k+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hm := Nat.mul_le_mul_right (paletteBound k h) hp
  change 2^(3*k) * paletteBound k h + 9*k ≤ 12*k + 2^(4*k+1)*paletteBound k h
  omega

@[simp] theorem paletteBound_zero_arity (h : Nat) : paletteBound 0 h = 0 := by
  induction h with
  | zero => rfl
  | succ h ih => simp [paletteBound,ih]
end StackSorting.GuidedPathwidth
