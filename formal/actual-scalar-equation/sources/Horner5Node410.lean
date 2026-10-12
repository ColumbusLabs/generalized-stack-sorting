import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p410 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 16)]]

theorem h5n410_arithmetic : BiPoly.mul h5p358 h5p9=h5p410 := by
  decide +kernel

theorem h5n410 : h5e410.toBi mapPolyEnv=h5p410 := by
  change BiPoly.mul (h5e358.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p410
  rw [h5n358, h5n9]
  exact h5n410_arithmetic

#print axioms h5n410_arithmetic
end StackSorting.RationalLift
