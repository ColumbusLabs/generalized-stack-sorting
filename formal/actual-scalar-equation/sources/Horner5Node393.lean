import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p393 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 7)]]

theorem h5n393_arithmetic : BiPoly.mul h5p355 h5p9=h5p393 := by
  decide +kernel

theorem h5n393 : h5e393.toBi mapPolyEnv=h5p393 := by
  change BiPoly.mul (h5e355.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p393
  rw [h5n355, h5n9]
  exact h5n393_arithmetic

#print axioms h5n393_arithmetic
end StackSorting.RationalLift
