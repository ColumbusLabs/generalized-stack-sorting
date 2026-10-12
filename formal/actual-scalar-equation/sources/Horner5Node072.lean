import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p72 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 180)]]

theorem h5n72_arithmetic : BiPoly.mul h5p71 h5p9=h5p72 := by
  decide +kernel

theorem h5n72 : h5e72.toBi mapPolyEnv=h5p72 := by
  change BiPoly.mul (h5e71.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p72
  rw [h5n71, h5n9]
  exact h5n72_arithmetic

#print axioms h5n72_arithmetic
end StackSorting.RationalLift
