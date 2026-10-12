import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p13 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 95)]]

theorem h5n13_arithmetic : BiPoly.mul h5p8 h5p11=h5p13 := by
  decide +kernel

theorem h5n13 : h5e13.toBi mapPolyEnv=h5p13 := by
  change BiPoly.mul (h5e8.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p13
  rw [h5n8, h5n11]
  exact h5n13_arithmetic

#print axioms h5n13_arithmetic
end StackSorting.RationalLift
