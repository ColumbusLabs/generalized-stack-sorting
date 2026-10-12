import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p128 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 35)]]

theorem h5n128_arithmetic : BiPoly.mul h5p113 h5p11=h5p128 := by
  decide +kernel

theorem h5n128 : h5e128.toBi mapPolyEnv=h5p128 := by
  change BiPoly.mul (h5e113.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p128
  rw [h5n113, h5n11]
  exact h5n128_arithmetic

#print axioms h5n128_arithmetic
end StackSorting.RationalLift
