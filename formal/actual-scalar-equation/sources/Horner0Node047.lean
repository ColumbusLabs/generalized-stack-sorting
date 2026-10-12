import Horner0Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p47 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 12)]]

theorem h0n47_arithmetic : BiPoly.mul h0p46 h0p12=h0p47 := by
  decide +kernel

theorem h0n47 : h0e47.toBi mapPolyEnv=h0p47 := by
  change BiPoly.mul (h0e46.toBi mapPolyEnv) (h0e12.toBi mapPolyEnv)=h0p47
  rw [h0n46, h0n12]
  exact h0n47_arithmetic

#print axioms h0n47_arithmetic
end StackSorting.RationalLift
