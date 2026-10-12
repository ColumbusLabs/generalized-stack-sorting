import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p15 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 288)]]

theorem h5n15_arithmetic : BiPoly.mul h5p14 h5p9=h5p15 := by
  decide +kernel

theorem h5n15 : h5e15.toBi mapPolyEnv=h5p15 := by
  change BiPoly.mul (h5e14.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p15
  rw [h5n14, h5n9]
  exact h5n15_arithmetic

#print axioms h5n15_arithmetic
end StackSorting.RationalLift
