import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p359 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 8)]]

theorem h5n359_arithmetic : BiPoly.mul h5p356 h5p11=h5p359 := by
  decide +kernel

theorem h5n359 : h5e359.toBi mapPolyEnv=h5p359 := by
  change BiPoly.mul (h5e356.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p359
  rw [h5n356, h5n11]
  exact h5n359_arithmetic

#print axioms h5n359_arithmetic
end StackSorting.RationalLift
