import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p147 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 288)]]

theorem h4n147_arithmetic : BiPoly.mul h4p146 h4p9=h4p147 := by
  decide +kernel

theorem h4n147 : h4e147.toBi mapPolyEnv=h4p147 := by
  change BiPoly.mul (h4e146.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p147
  rw [h4n146, h4n9]
  exact h4n147_arithmetic

#print axioms h4n147_arithmetic
end StackSorting.RationalLift
