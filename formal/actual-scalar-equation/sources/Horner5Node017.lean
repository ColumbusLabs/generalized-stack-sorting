import Horner5Base
import Horner5Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p17 : BiPoly.Poly := [[(Int.negSucc 191), (Int.negSucc 95)], [(Int.ofNat 288)]]

theorem h5n17_arithmetic : BiPoly.add h5p12 h5p16=h5p17 := by
  decide +kernel

theorem h5n17 : h5e17.toBi mapPolyEnv=h5p17 := by
  change BiPoly.add (h5e12.toBi mapPolyEnv) (h5e16.toBi mapPolyEnv)=h5p17
  rw [h5n12, h5n16]
  exact h5n17_arithmetic

#print axioms h5n17_arithmetic
end StackSorting.RationalLift
