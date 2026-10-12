import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p337 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 60)]]

theorem h5n337_arithmetic : BiPoly.mul h5p183 h5p11=h5p337 := by
  decide +kernel

theorem h5n337 : h5e337.toBi mapPolyEnv=h5p337 := by
  change BiPoly.mul (h5e183.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p337
  rw [h5n183, h5n11]
  exact h5n337_arithmetic

#print axioms h5n337_arithmetic
end StackSorting.RationalLift
