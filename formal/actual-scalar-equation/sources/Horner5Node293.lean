import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p293 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 32)]]

theorem h5n293_arithmetic : BiPoly.mul h5p292 h5p9=h5p293 := by
  decide +kernel

theorem h5n293 : h5e293.toBi mapPolyEnv=h5p293 := by
  change BiPoly.mul (h5e292.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p293
  rw [h5n292, h5n9]
  exact h5n293_arithmetic

#print axioms h5n293_arithmetic
end StackSorting.RationalLift
