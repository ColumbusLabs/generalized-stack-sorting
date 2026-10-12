import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p318 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 48)]]

theorem h5n318_arithmetic : BiPoly.mul h5p191 h5p9=h5p318 := by
  decide +kernel

theorem h5n318 : h5e318.toBi mapPolyEnv=h5p318 := by
  change BiPoly.mul (h5e191.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p318
  rw [h5n191, h5n9]
  exact h5n318_arithmetic

#print axioms h5n318_arithmetic
end StackSorting.RationalLift
