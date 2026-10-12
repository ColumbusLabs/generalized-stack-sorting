import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p16 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 95)]]

theorem h4n16_arithmetic : BiPoly.mul h4p15 h4p9=h4p16 := by
  decide +kernel

theorem h4n16 : h4e16.toBi mapPolyEnv=h4p16 := by
  change BiPoly.mul (h4e15.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p16
  rw [h4n15, h4n9]
  exact h4n16_arithmetic

#print axioms h4n16_arithmetic
end StackSorting.RationalLift
