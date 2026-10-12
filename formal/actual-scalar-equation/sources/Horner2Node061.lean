import Horner2Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p61 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 11)]]

theorem h2n61_arithmetic : BiPoly.mul h2p49 h2p8=h2p61 := by
  decide +kernel

theorem h2n61 : h2e61.toBi mapPolyEnv=h2p61 := by
  change BiPoly.mul (h2e49.toBi mapPolyEnv) (h2e8.toBi mapPolyEnv)=h2p61
  rw [h2n49, h2n8]
  exact h2n61_arithmetic

#print axioms h2n61_arithmetic
end StackSorting.RationalLift
