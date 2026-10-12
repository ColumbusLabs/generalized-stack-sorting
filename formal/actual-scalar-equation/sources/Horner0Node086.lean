import Horner0Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p86 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 48)]]

theorem h0n86_arithmetic : BiPoly.mul h0p11 h0p12=h0p86 := by
  decide +kernel

theorem h0n86 : h0e86.toBi mapPolyEnv=h0p86 := by
  change BiPoly.mul (h0e11.toBi mapPolyEnv) (h0e12.toBi mapPolyEnv)=h0p86
  rw [h0n11, h0n12]
  exact h0n86_arithmetic

#print axioms h0n86_arithmetic
end StackSorting.RationalLift
