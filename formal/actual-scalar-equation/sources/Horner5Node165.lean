import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p165 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 12)]]

theorem h5n165_arithmetic : BiPoly.mul h5p164 h5p9=h5p165 := by
  decide +kernel

theorem h5n165 : h5e165.toBi mapPolyEnv=h5p165 := by
  change BiPoly.mul (h5e164.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p165
  rw [h5n164, h5n9]
  exact h5n165_arithmetic

#print axioms h5n165_arithmetic
end StackSorting.RationalLift
