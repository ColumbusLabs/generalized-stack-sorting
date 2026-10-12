import Horner1Base
import Horner1Node095
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p96 : BiPoly.Poly := [[(Int.negSucc 3), (Int.negSucc 31)]]

theorem h1n96_arithmetic : BiPoly.add h1p64 h1p95=h1p96 := by
  decide +kernel

theorem h1n96 : h1e96.toBi mapPolyEnv=h1p96 := by
  change BiPoly.add (h1e64.toBi mapPolyEnv) (h1e95.toBi mapPolyEnv)=h1p96
  rw [h1n64, h1n95]
  exact h1n96_arithmetic

#print axioms h1n96_arithmetic
end StackSorting.RationalLift
