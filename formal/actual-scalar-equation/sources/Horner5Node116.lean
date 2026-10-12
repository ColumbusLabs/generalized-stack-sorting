import Horner5Base
import Horner5Node026
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p116 : BiPoly.Poly := [[(Int.ofNat 36)], [(Int.negSucc 71)]]

theorem h5n116_arithmetic : BiPoly.add h5p114 h5p26=h5p116 := by
  decide +kernel

theorem h5n116 : h5e116.toBi mapPolyEnv=h5p116 := by
  change BiPoly.add (h5e114.toBi mapPolyEnv) (h5e26.toBi mapPolyEnv)=h5p116
  rw [h5n114, h5n26]
  exact h5n116_arithmetic

#print axioms h5n116_arithmetic
end StackSorting.RationalLift
