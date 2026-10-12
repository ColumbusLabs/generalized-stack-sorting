import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p387 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 11)]]

theorem h5n387_arithmetic : BiPoly.mul h5p163 h5p11=h5p387 := by
  decide +kernel

theorem h5n387 : h5e387.toBi mapPolyEnv=h5p387 := by
  change BiPoly.mul (h5e163.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p387
  rw [h5n163, h5n11]
  exact h5n387_arithmetic

#print axioms h5n387_arithmetic
end StackSorting.RationalLift
