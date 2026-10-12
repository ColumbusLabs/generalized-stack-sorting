import Horner5Base
import Horner5Node118
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p119 : BiPoly.Poly := [[(Int.negSucc 35), (Int.ofNat 36)], [(Int.ofNat 36), (Int.negSucc 71)]]

theorem h5n119_arithmetic : BiPoly.add h5p113 h5p118=h5p119 := by
  decide +kernel

theorem h5n119 : h5e119.toBi mapPolyEnv=h5p119 := by
  change BiPoly.add (h5e113.toBi mapPolyEnv) (h5e118.toBi mapPolyEnv)=h5p119
  rw [h5n113, h5n118]
  exact h5n119_arithmetic

#print axioms h5n119_arithmetic
end StackSorting.RationalLift
