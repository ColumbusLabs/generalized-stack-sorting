import Horner5Base
import Horner5Node028
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p29 : BiPoly.Poly := [[(Int.ofNat 72), (Int.ofNat 72)], [(Int.negSucc 71)]]

theorem h5n29_arithmetic : BiPoly.add h5p24 h5p28=h5p29 := by
  decide +kernel

theorem h5n29 : h5e29.toBi mapPolyEnv=h5p29 := by
  change BiPoly.add (h5e24.toBi mapPolyEnv) (h5e28.toBi mapPolyEnv)=h5p29
  rw [h5n24, h5n28]
  exact h5n29_arithmetic

#print axioms h5n29_arithmetic
end StackSorting.RationalLift
