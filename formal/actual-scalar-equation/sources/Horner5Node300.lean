import Horner5Base
import Horner5Node299
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p300 : BiPoly.Poly := [[(Int.negSucc 31), (Int.ofNat 64), (Int.ofNat 32)], [(Int.ofNat 32), (Int.negSucc 95)]]

theorem h5n300_arithmetic : BiPoly.add h5p291 h5p299=h5p300 := by
  decide +kernel

theorem h5n300 : h5e300.toBi mapPolyEnv=h5p300 := by
  change BiPoly.add (h5e291.toBi mapPolyEnv) (h5e299.toBi mapPolyEnv)=h5p300
  rw [h5n291, h5n299]
  exact h5n300_arithmetic

#print axioms h5n300_arithmetic
end StackSorting.RationalLift
