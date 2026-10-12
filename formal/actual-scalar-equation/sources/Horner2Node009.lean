import Horner2Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p9 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 48)]]

theorem h2n9_arithmetic : BiPoly.mul h2p7 h2p8=h2p9 := by
  decide +kernel

theorem h2n9 : h2e9.toBi mapPolyEnv=h2p9 := by
  change BiPoly.mul (h2e7.toBi mapPolyEnv) (h2e8.toBi mapPolyEnv)=h2p9
  rw [h2n7, h2n8]
  exact h2n9_arithmetic

#print axioms h2n9_arithmetic
end StackSorting.RationalLift
