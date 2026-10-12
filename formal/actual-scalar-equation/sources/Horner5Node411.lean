import Horner5Base
import Horner5Node329
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p411 : BiPoly.Poly := [[(Int.negSucc 15), (Int.negSucc 31)]]

theorem h5n411_arithmetic : BiPoly.add h5p409 h5p329=h5p411 := by
  decide +kernel

theorem h5n411 : h5e411.toBi mapPolyEnv=h5p411 := by
  change BiPoly.add (h5e409.toBi mapPolyEnv) (h5e329.toBi mapPolyEnv)=h5p411
  rw [h5n409, h5n329]
  exact h5n411_arithmetic

#print axioms h5n411_arithmetic
end StackSorting.RationalLift
