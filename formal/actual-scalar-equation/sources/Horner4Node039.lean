import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p39 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 96)]]

theorem h4n39_arithmetic : BiPoly.mul h4p14 h4p9=h4p39 := by
  decide +kernel

theorem h4n39 : h4e39.toBi mapPolyEnv=h4p39 := by
  change BiPoly.mul (h4e14.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p39
  rw [h4n14, h4n9]
  exact h4n39_arithmetic

#print axioms h4n39_arithmetic
end StackSorting.RationalLift
