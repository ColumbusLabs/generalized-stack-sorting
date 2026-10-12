import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p394 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 16)]]

theorem h5n394_arithmetic : BiPoly.mul h5p358 h5p11=h5p394 := by
  decide +kernel

theorem h5n394 : h5e394.toBi mapPolyEnv=h5p394 := by
  change BiPoly.mul (h5e358.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p394
  rw [h5n358, h5n11]
  exact h5n394_arithmetic

#print axioms h5n394_arithmetic
end StackSorting.RationalLift
