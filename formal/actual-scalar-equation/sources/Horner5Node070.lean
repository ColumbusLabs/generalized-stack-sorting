import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p70 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 179)]]

theorem h5n70_arithmetic : BiPoly.mul h5p69 h5p11=h5p70 := by
  decide +kernel

theorem h5n70 : h5e70.toBi mapPolyEnv=h5p70 := by
  change BiPoly.mul (h5e69.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p70
  rw [h5n69, h5n11]
  exact h5n70_arithmetic

#print axioms h5n70_arithmetic
end StackSorting.RationalLift
