import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p62 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 96)]]

theorem h5n62_arithmetic : BiPoly.mul h5p7 h5p11=h5p62 := by
  decide +kernel

theorem h5n62 : h5e62.toBi mapPolyEnv=h5p62 := by
  change BiPoly.mul (h5e7.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p62
  rw [h5n7, h5n11]
  exact h5n62_arithmetic

#print axioms h5n62_arithmetic
end StackSorting.RationalLift
