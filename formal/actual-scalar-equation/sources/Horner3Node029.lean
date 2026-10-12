import Horner3Base
import Horner3Node028
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h3p29 : BiPoly.Poly := [[-3,-3]]

theorem h3n29_arithmetic : BiPoly.add h3p27 h3p28=h3p29 := by
  decide +kernel

theorem h3n29 : h3e29.toBi mapPolyEnv=h3p29 := by
  change BiPoly.add (h3e27.toBi mapPolyEnv) (h3e28.toBi mapPolyEnv)=h3p29
  rw [h3n27, h3n28]
  exact h3n29_arithmetic

#print axioms h3n29_arithmetic
end StackSorting.RationalLift
