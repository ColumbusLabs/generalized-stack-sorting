import Horner5Base
import Horner5Node360
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p361 : BiPoly.Poly := [[(Int.ofNat 16), (Int.ofNat 8)], [(Int.negSucc 23)]]

theorem h5n361_arithmetic : BiPoly.add h5p358 h5p360=h5p361 := by
  decide +kernel

theorem h5n361 : h5e361.toBi mapPolyEnv=h5p361 := by
  change BiPoly.add (h5e358.toBi mapPolyEnv) (h5e360.toBi mapPolyEnv)=h5p361
  rw [h5n358, h5n360]
  exact h5n361_arithmetic

#print axioms h5n361_arithmetic
end StackSorting.RationalLift
