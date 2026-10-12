import Horner4Base
import Horner4Node227
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p228 : BiPoly.Poly := [[(Int.negSucc 7), (Int.ofNat 8)]]

theorem h4n228_arithmetic : BiPoly.add h4p225 h4p227=h4p228 := by
  decide +kernel

theorem h4n228 : h4e228.toBi mapPolyEnv=h4p228 := by
  change BiPoly.add (h4e225.toBi mapPolyEnv) (h4e227.toBi mapPolyEnv)=h4p228
  rw [h4n225, h4n227]
  exact h4n228_arithmetic

#print axioms h4n228_arithmetic
end StackSorting.RationalLift
