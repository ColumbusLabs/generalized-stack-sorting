import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p156 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 17)]]

theorem h5n156_arithmetic : BiPoly.mul h5p155 h5p9=h5p156 := by
  decide +kernel

theorem h5n156 : h5e156.toBi mapPolyEnv=h5p156 := by
  change BiPoly.mul (h5e155.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p156
  rw [h5n155, h5n9]
  exact h5n156_arithmetic

#print axioms h5n156_arithmetic
end StackSorting.RationalLift
