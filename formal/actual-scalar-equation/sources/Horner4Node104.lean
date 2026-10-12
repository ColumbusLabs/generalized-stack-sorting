import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p104 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 35)]]

theorem h4n104_arithmetic : BiPoly.mul h4p61 h4p9=h4p104 := by
  decide +kernel

theorem h4n104 : h4e104.toBi mapPolyEnv=h4p104 := by
  change BiPoly.mul (h4e61.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p104
  rw [h4n61, h4n9]
  exact h4n104_arithmetic

#print axioms h4n104_arithmetic
end StackSorting.RationalLift
