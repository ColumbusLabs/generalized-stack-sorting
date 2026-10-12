import Horner5Base
import Horner5Node227
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p228 : BiPoly.Poly := [[(Int.negSucc 215), (Int.negSucc 215)], [(Int.ofNat 216)]]

theorem h5n228_arithmetic : BiPoly.add h5p207 h5p227=h5p228 := by
  decide +kernel

theorem h5n228 : h5e228.toBi mapPolyEnv=h5p228 := by
  change BiPoly.add (h5e207.toBi mapPolyEnv) (h5e227.toBi mapPolyEnv)=h5p228
  rw [h5n207, h5n227]
  exact h5n228_arithmetic

#print axioms h5n228_arithmetic
end StackSorting.RationalLift
