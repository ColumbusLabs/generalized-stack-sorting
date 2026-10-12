import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p215 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 287)]]

theorem h5n215_arithmetic : BiPoly.mul h5p38 h5p11=h5p215 := by
  decide +kernel

theorem h5n215 : h5e215.toBi mapPolyEnv=h5p215 := by
  change BiPoly.mul (h5e38.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p215
  rw [h5n38, h5n11]
  exact h5n215_arithmetic

#print axioms h5n215_arithmetic
end StackSorting.RationalLift
