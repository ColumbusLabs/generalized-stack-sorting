import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p374 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 11)]]

theorem h5n374_arithmetic : BiPoly.mul h5p163 h5p9=h5p374 := by
  decide +kernel

theorem h5n374 : h5e374.toBi mapPolyEnv=h5p374 := by
  change BiPoly.mul (h5e163.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p374
  rw [h5n163, h5n9]
  exact h5n374_arithmetic

#print axioms h5n374_arithmetic
end StackSorting.RationalLift
