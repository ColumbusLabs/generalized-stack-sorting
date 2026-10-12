import Horner3Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h3p28 : BiPoly.Poly := [[0,-3]]

theorem h3n28_arithmetic : BiPoly.mul h3p27 h3p9=h3p28 := by
  decide +kernel

theorem h3n28 : h3e28.toBi mapPolyEnv=h3p28 := by
  change BiPoly.mul (h3e27.toBi mapPolyEnv) (h3e9.toBi mapPolyEnv)=h3p28
  rw [h3n27, h3n9]
  exact h3n28_arithmetic

#print axioms h3n28_arithmetic
end StackSorting.RationalLift
