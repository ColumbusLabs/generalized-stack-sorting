import Horner4Base
import Horner4Node016
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p17 : BiPoly.Poly := [[(Int.ofNat 96), (Int.negSucc 95)]]

theorem h4n17_arithmetic : BiPoly.add h4p14 h4p16=h4p17 := by
  decide +kernel

theorem h4n17 : h4e17.toBi mapPolyEnv=h4p17 := by
  change BiPoly.add (h4e14.toBi mapPolyEnv) (h4e16.toBi mapPolyEnv)=h4p17
  rw [h4n14, h4n16]
  exact h4n17_arithmetic

#print axioms h4n17_arithmetic
end StackSorting.RationalLift
