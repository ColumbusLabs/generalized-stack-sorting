import Horner2Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p23 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 95)]]

theorem h2n23_arithmetic : BiPoly.mul h2p22 h2p8=h2p23 := by
  decide +kernel

theorem h2n23 : h2e23.toBi mapPolyEnv=h2p23 := by
  change BiPoly.mul (h2e22.toBi mapPolyEnv) (h2e8.toBi mapPolyEnv)=h2p23
  rw [h2n22, h2n8]
  exact h2n23_arithmetic

#print axioms h2n23_arithmetic
end StackSorting.RationalLift
