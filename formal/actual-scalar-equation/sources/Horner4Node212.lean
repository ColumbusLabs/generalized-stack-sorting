import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p212 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 31)]]

theorem h4n212_arithmetic : BiPoly.mul h4p195 h4p9=h4p212 := by
  decide +kernel

theorem h4n212 : h4e212.toBi mapPolyEnv=h4p212 := by
  change BiPoly.mul (h4e195.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p212
  rw [h4n195, h4n9]
  exact h4n212_arithmetic

#print axioms h4n212_arithmetic
end StackSorting.RationalLift
