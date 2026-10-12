import Horner1Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p95 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 31)]]

theorem h1n95_arithmetic : BiPoly.mul h1p94 h1p9=h1p95 := by
  decide +kernel

theorem h1n95 : h1e95.toBi mapPolyEnv=h1p95 := by
  change BiPoly.mul (h1e94.toBi mapPolyEnv) (h1e9.toBi mapPolyEnv)=h1p95
  rw [h1n94, h1n9]
  exact h1n95_arithmetic

#print axioms h1n95_arithmetic
end StackSorting.RationalLift
