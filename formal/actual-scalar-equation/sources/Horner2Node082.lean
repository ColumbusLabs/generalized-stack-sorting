import Horner2Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p82 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 32)]]

theorem h2n82_arithmetic : BiPoly.mul h2p81 h2p8=h2p82 := by
  decide +kernel

theorem h2n82 : h2e82.toBi mapPolyEnv=h2p82 := by
  change BiPoly.mul (h2e81.toBi mapPolyEnv) (h2e8.toBi mapPolyEnv)=h2p82
  rw [h2n81, h2n8]
  exact h2n82_arithmetic

#print axioms h2n82_arithmetic
end StackSorting.RationalLift
