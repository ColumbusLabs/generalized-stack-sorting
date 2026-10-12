import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p327 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 31)]]

theorem h5n327_arithmetic : BiPoly.mul h5p291 h5p9=h5p327 := by
  decide +kernel

theorem h5n327 : h5e327.toBi mapPolyEnv=h5p327 := by
  change BiPoly.mul (h5e291.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p327
  rw [h5n291, h5n9]
  exact h5n327_arithmetic

#print axioms h5n327_arithmetic
end StackSorting.RationalLift
