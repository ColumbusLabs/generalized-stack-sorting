import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p357 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 8)]]

theorem h5n357_arithmetic : BiPoly.mul h5p356 h5p9=h5p357 := by
  decide +kernel

theorem h5n357 : h5e357.toBi mapPolyEnv=h5p357 := by
  change BiPoly.mul (h5e356.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p357
  rw [h5n356, h5n9]
  exact h5n357_arithmetic

#print axioms h5n357_arithmetic
end StackSorting.RationalLift
