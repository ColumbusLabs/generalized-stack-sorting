import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p197 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 32)]]

theorem h4n197_arithmetic : BiPoly.mul h4p196 h4p9=h4p197 := by
  decide +kernel

theorem h4n197 : h4e197.toBi mapPolyEnv=h4p197 := by
  change BiPoly.mul (h4e196.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p197
  rw [h4n196, h4n9]
  exact h4n197_arithmetic

#print axioms h4n197_arithmetic
end StackSorting.RationalLift
