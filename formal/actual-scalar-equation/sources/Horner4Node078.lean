import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p78 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 24)]]

theorem h4n78_arithmetic : BiPoly.mul h4p53 h4p9=h4p78 := by
  decide +kernel

theorem h4n78 : h4e78.toBi mapPolyEnv=h4p78 := by
  change BiPoly.mul (h4e53.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p78
  rw [h4n53, h4n9]
  exact h4n78_arithmetic

#print axioms h4n78_arithmetic
end StackSorting.RationalLift
