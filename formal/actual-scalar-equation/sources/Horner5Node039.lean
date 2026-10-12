import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p39 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 287)]]

theorem h5n39_arithmetic : BiPoly.mul h5p38 h5p9=h5p39 := by
  decide +kernel

theorem h5n39 : h5e39.toBi mapPolyEnv=h5p39 := by
  change BiPoly.mul (h5e38.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p39
  rw [h5n38, h5n9]
  exact h5n39_arithmetic

#print axioms h5n39_arithmetic
end StackSorting.RationalLift
