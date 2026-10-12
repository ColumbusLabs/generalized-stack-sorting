import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p367 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 18)]]

theorem h5n367_arithmetic : BiPoly.mul h5p154 h5p9=h5p367 := by
  decide +kernel

theorem h5n367 : h5e367.toBi mapPolyEnv=h5p367 := by
  change BiPoly.mul (h5e154.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p367
  rw [h5n154, h5n9]
  exact h5n367_arithmetic

#print axioms h5n367_arithmetic
end StackSorting.RationalLift
