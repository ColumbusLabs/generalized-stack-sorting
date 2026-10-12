import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p246 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 54)]]

theorem h5n246_arithmetic : BiPoly.mul h5p103 h5p9=h5p246 := by
  decide +kernel

theorem h5n246 : h5e246.toBi mapPolyEnv=h5p246 := by
  change BiPoly.mul (h5e103.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p246
  rw [h5n103, h5n9]
  exact h5n246_arithmetic

#print axioms h5n246_arithmetic
end StackSorting.RationalLift
