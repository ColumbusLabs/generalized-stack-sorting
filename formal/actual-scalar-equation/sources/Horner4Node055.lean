import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p55 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 23)]]

theorem h4n55_arithmetic : BiPoly.mul h4p54 h4p9=h4p55 := by
  decide +kernel

theorem h4n55 : h4e55.toBi mapPolyEnv=h4p55 := by
  change BiPoly.mul (h4e54.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p55
  rw [h4n54, h4n9]
  exact h4n55_arithmetic

#print axioms h4n55_arithmetic
end StackSorting.RationalLift
