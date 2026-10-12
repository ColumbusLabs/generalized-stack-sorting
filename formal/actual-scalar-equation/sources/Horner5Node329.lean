import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p329 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 31)]]

theorem h5n329_arithmetic : BiPoly.mul h5p291 h5p11=h5p329 := by
  decide +kernel

theorem h5n329 : h5e329.toBi mapPolyEnv=h5p329 := by
  change BiPoly.mul (h5e291.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p329
  rw [h5n291, h5n11]
  exact h5n329_arithmetic

#print axioms h5n329_arithmetic
end StackSorting.RationalLift
