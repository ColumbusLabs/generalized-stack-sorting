import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p26 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 71)]]

theorem h5n26_arithmetic : BiPoly.mul h5p25 h5p9=h5p26 := by
  decide +kernel

theorem h5n26 : h5e26.toBi mapPolyEnv=h5p26 := by
  change BiPoly.mul (h5e25.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p26
  rw [h5n25, h5n9]
  exact h5n26_arithmetic

#print axioms h5n26_arithmetic
end StackSorting.RationalLift
