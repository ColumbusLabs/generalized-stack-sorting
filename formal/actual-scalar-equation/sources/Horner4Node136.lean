import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p136 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 287)]]

theorem h4n136_arithmetic : BiPoly.mul h4p135 h4p9=h4p136 := by
  decide +kernel

theorem h4n136 : h4e136.toBi mapPolyEnv=h4p136 := by
  change BiPoly.mul (h4e135.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p136
  rw [h4n135, h4n9]
  exact h4n136_arithmetic

#print axioms h4n136_arithmetic
end StackSorting.RationalLift
