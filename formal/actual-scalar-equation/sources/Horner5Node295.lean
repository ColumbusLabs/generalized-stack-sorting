import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p295 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 32)]]

theorem h5n295_arithmetic : BiPoly.mul h5p292 h5p11=h5p295 := by
  decide +kernel

theorem h5n295 : h5e295.toBi mapPolyEnv=h5p295 := by
  change BiPoly.mul (h5e292.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p295
  rw [h5n292, h5n11]
  exact h5n295_arithmetic

#print axioms h5n295_arithmetic
end StackSorting.RationalLift
