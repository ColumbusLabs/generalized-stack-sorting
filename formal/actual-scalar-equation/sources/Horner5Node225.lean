import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p225 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 215)]]

theorem h5n225_arithmetic : BiPoly.mul h5p207 h5p11=h5p225 := by
  decide +kernel

theorem h5n225 : h5e225.toBi mapPolyEnv=h5p225 := by
  change BiPoly.mul (h5e207.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p225
  rw [h5n207, h5n11]
  exact h5n225_arithmetic

#print axioms h5n225_arithmetic
end StackSorting.RationalLift
