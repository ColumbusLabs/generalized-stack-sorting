import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p106 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 54)]]

theorem h5n106_arithmetic : BiPoly.mul h5p103 h5p11=h5p106 := by
  decide +kernel

theorem h5n106 : h5e106.toBi mapPolyEnv=h5p106 := by
  change BiPoly.mul (h5e103.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p106
  rw [h5n103, h5n11]
  exact h5n106_arithmetic

#print axioms h5n106_arithmetic
end StackSorting.RationalLift
