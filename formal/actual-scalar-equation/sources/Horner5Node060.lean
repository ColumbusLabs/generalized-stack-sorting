import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p60 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 96)]]

theorem h5n60_arithmetic : BiPoly.mul h5p7 h5p9=h5p60 := by
  decide +kernel

theorem h5n60 : h5e60.toBi mapPolyEnv=h5p60 := by
  change BiPoly.mul (h5e7.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p60
  rw [h5n7, h5n9]
  exact h5n60_arithmetic

#print axioms h5n60_arithmetic
end StackSorting.RationalLift
