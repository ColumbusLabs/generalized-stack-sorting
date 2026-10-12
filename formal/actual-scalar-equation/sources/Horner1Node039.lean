import Horner1Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p39 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 47)]]

theorem h1n39_arithmetic : BiPoly.mul h1p38 h1p9=h1p39 := by
  decide +kernel

theorem h1n39 : h1e39.toBi mapPolyEnv=h1p39 := by
  change BiPoly.mul (h1e38.toBi mapPolyEnv) (h1e9.toBi mapPolyEnv)=h1p39
  rw [h1n38, h1n9]
  exact h1n39_arithmetic

#print axioms h1n39_arithmetic
end StackSorting.RationalLift
