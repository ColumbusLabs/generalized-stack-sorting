import FPSDivision
namespace StackSorting.FPSDivision
open StackSorting.CauchyRing

theorem add_constant (a b : FPS) : (a+b) 0 = a 0+b 0 := rfl

theorem neg_constant (a : FPS) : (-a) 0 = -(a 0) := rfl

theorem sub_constant (a b : FPS) : (a-b) 0 = a 0-b 0 := by
  change a 0 + -(b 0) = a 0-b 0
  grind

theorem mul_constant (a b : FPS) : (a*b) 0 = a 0*b 0 :=
  cauchy_zero a.coeff b.coeff

theorem numeral_constant (n : Nat) :
    (OfNat.ofNat (α := FPS) n) 0 = OfNat.ofNat (α := Rat) n := rfl

theorem C_constant (c : Rat) : C c 0=c := rfl

theorem X_constant : X 0=0 := rfl

theorem pow_constant (a : FPS) (k : Nat) : (a^k) 0=(a 0)^k := by
  induction k with
  | zero => change (1 : Rat) = (a 0)^0; grind
  | succ k ih =>
    change (a^k*a) 0 = (a 0)^(k+1)
    rw [mul_constant, ih]
    grind

end StackSorting.FPSDivision
