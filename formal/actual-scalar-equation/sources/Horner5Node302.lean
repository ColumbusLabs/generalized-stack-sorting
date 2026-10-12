import Horner5Node095
import Horner5Node135
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p302 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 23)], [(Int.ofNat 24)]]

theorem h5n302_arithmetic : BiPoly.add h5p95 h5p135=h5p302 := by
  decide +kernel

theorem h5n302 : h5e302.toBi mapPolyEnv=h5p302 := by
  change BiPoly.add (h5e95.toBi mapPolyEnv) (h5e135.toBi mapPolyEnv)=h5p302
  rw [h5n95, h5n135]
  exact h5n302_arithmetic

#print axioms h5n302_arithmetic
end StackSorting.RationalLift
