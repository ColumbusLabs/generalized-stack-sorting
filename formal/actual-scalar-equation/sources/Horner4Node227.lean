import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p227 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 8)]]

theorem h4n227_arithmetic : BiPoly.mul h4p226 h4p9=h4p227 := by
  decide +kernel

theorem h4n227 : h4e227.toBi mapPolyEnv=h4p227 := by
  change BiPoly.mul (h4e226.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p227
  rw [h4n226, h4n9]
  exact h4n227_arithmetic

#print axioms h4n227_arithmetic
end StackSorting.RationalLift
