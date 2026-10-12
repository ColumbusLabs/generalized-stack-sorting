import Horner5Base
import Horner5Node135
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p375 : BiPoly.Poly := [[(Int.negSucc 11)], [(Int.ofNat 24)]]

theorem h5n375_arithmetic : BiPoly.add h5p163 h5p135=h5p375 := by
  decide +kernel

theorem h5n375 : h5e375.toBi mapPolyEnv=h5p375 := by
  change BiPoly.add (h5e163.toBi mapPolyEnv) (h5e135.toBi mapPolyEnv)=h5p375
  rw [h5n163, h5n135]
  exact h5n375_arithmetic

#print axioms h5n375_arithmetic
end StackSorting.RationalLift
