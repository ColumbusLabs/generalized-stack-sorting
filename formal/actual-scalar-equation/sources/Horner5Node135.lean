import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p135 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 24)]]

theorem h5n135_arithmetic : BiPoly.mul h5p91 h5p9=h5p135 := by
  decide +kernel

theorem h5n135 : h5e135.toBi mapPolyEnv=h5p135 := by
  change BiPoly.mul (h5e91.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p135
  rw [h5n91, h5n9]
  exact h5n135_arithmetic

#print axioms h5n135_arithmetic
end StackSorting.RationalLift
