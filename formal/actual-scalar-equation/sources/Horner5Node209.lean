import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p209 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 216)]]

theorem h5n209_arithmetic : BiPoly.mul h5p206 h5p11=h5p209 := by
  decide +kernel

theorem h5n209 : h5e209.toBi mapPolyEnv=h5p209 := by
  change BiPoly.mul (h5e206.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p209
  rw [h5n206, h5n11]
  exact h5n209_arithmetic

#print axioms h5n209_arithmetic
end StackSorting.RationalLift
