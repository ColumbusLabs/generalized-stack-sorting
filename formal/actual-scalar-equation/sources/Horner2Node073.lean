import Horner2Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p73 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 15)]]

theorem h2n73_arithmetic : BiPoly.mul h2p72 h2p8=h2p73 := by
  decide +kernel

theorem h2n73 : h2e73.toBi mapPolyEnv=h2p73 := by
  change BiPoly.mul (h2e72.toBi mapPolyEnv) (h2e8.toBi mapPolyEnv)=h2p73
  rw [h2n72, h2n8]
  exact h2n73_arithmetic

#print axioms h2n73_arithmetic
end StackSorting.RationalLift
