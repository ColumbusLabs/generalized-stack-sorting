import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p276 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 9)]]

theorem h5n276_arithmetic : BiPoly.mul h5p273 h5p11=h5p276 := by
  decide +kernel

theorem h5n276 : h5e276.toBi mapPolyEnv=h5p276 := by
  change BiPoly.mul (h5e273.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p276
  rw [h5n273, h5n11]
  exact h5n276_arithmetic

#print axioms h5n276_arithmetic
end StackSorting.RationalLift
