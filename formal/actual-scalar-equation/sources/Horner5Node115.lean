import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p115 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 36)]]

theorem h5n115_arithmetic : BiPoly.mul h5p114 h5p9=h5p115 := by
  decide +kernel

theorem h5n115 : h5e115.toBi mapPolyEnv=h5p115 := by
  change BiPoly.mul (h5e114.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p115
  rw [h5n114, h5n9]
  exact h5n115_arithmetic

#print axioms h5n115_arithmetic
end StackSorting.RationalLift
