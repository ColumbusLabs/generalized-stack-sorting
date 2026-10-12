import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p96 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 72)]]

theorem h5n96_arithmetic : BiPoly.mul h5p24 h5p9=h5p96 := by
  decide +kernel

theorem h5n96 : h5e96.toBi mapPolyEnv=h5p96 := by
  change BiPoly.mul (h5e24.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p96
  rw [h5n24, h5n9]
  exact h5n96_arithmetic

#print axioms h5n96_arithmetic
end StackSorting.RationalLift
