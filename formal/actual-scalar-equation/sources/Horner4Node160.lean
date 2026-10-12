import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p160 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 72)]]

theorem h4n160_arithmetic : BiPoly.mul h4p6 h4p9=h4p160 := by
  decide +kernel

theorem h4n160 : h4e160.toBi mapPolyEnv=h4p160 := by
  change BiPoly.mul (h4e6.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p160
  rw [h4n6, h4n9]
  exact h4n160_arithmetic

#print axioms h4n160_arithmetic
end StackSorting.RationalLift
