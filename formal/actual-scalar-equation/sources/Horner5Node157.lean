import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p157 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 18)]]

theorem h5n157_arithmetic : BiPoly.mul h5p154 h5p11=h5p157 := by
  decide +kernel

theorem h5n157 : h5e157.toBi mapPolyEnv=h5p157 := by
  change BiPoly.mul (h5e154.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p157
  rw [h5n154, h5n11]
  exact h5n157_arithmetic

#print axioms h5n157_arithmetic
end StackSorting.RationalLift
