import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p366 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 17)]]

theorem h5n366_arithmetic : BiPoly.mul h5p155 h5p11=h5p366 := by
  decide +kernel

theorem h5n366 : h5e366.toBi mapPolyEnv=h5p366 := by
  change BiPoly.mul (h5e155.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p366
  rw [h5n155, h5n11]
  exact h5n366_arithmetic

#print axioms h5n366_arithmetic
end StackSorting.RationalLift
