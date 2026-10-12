import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p232 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 288)]]

theorem h5n232_arithmetic : BiPoly.mul h5p14 h5p11=h5p232 := by
  decide +kernel

theorem h5n232 : h5e232.toBi mapPolyEnv=h5p232 := by
  change BiPoly.mul (h5e14.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p232
  rw [h5n14, h5n11]
  exact h5n232_arithmetic

#print axioms h5n232_arithmetic
end StackSorting.RationalLift
