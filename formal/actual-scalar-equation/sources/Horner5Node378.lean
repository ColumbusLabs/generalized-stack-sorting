import Horner5Base
import Horner5Node377
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p378 : BiPoly.Poly := [[(Int.ofNat 12), (Int.negSucc 11)], [(Int.negSucc 11), (Int.ofNat 24)]]

theorem h5n378_arithmetic : BiPoly.add h5p164 h5p377=h5p378 := by
  decide +kernel

theorem h5n378 : h5e378.toBi mapPolyEnv=h5p378 := by
  change BiPoly.add (h5e164.toBi mapPolyEnv) (h5e377.toBi mapPolyEnv)=h5p378
  rw [h5n164, h5n377]
  exact h5n378_arithmetic

#print axioms h5n378_arithmetic
end StackSorting.RationalLift
