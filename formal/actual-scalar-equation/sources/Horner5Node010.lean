import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p10 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 95)]]

theorem h5n10_arithmetic : BiPoly.mul h5p8 h5p9=h5p10 := by
  decide +kernel

theorem h5n10 : h5e10.toBi mapPolyEnv=h5p10 := by
  change BiPoly.mul (h5e8.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p10
  rw [h5n8, h5n9]
  exact h5n10_arithmetic

#print axioms h5n10_arithmetic
end StackSorting.RationalLift
