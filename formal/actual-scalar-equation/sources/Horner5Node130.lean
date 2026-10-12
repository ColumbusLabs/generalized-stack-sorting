import Horner5Base
import Horner5Node129
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p130 : BiPoly.Poly := [[(Int.negSucc 35), (Int.negSucc 35)], [(Int.ofNat 36)]]

theorem h5n130_arithmetic : BiPoly.add h5p113 h5p129=h5p130 := by
  decide +kernel

theorem h5n130 : h5e130.toBi mapPolyEnv=h5p130 := by
  change BiPoly.add (h5e113.toBi mapPolyEnv) (h5e129.toBi mapPolyEnv)=h5p130
  rw [h5n113, h5n129]
  exact h5n130_arithmetic

#print axioms h5n130_arithmetic
end StackSorting.RationalLift
