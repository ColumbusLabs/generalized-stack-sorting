import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p192 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 47)]]

theorem h5n192_arithmetic : BiPoly.mul h5p94 h5p9=h5p192 := by
  decide +kernel

theorem h5n192 : h5e192.toBi mapPolyEnv=h5p192 := by
  change BiPoly.mul (h5e94.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p192
  rw [h5n94, h5n9]
  exact h5n192_arithmetic

#print axioms h5n192_arithmetic
end StackSorting.RationalLift
