import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p27 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 72)]]

theorem h5n27_arithmetic : BiPoly.mul h5p24 h5p11=h5p27 := by
  decide +kernel

theorem h5n27 : h5e27.toBi mapPolyEnv=h5p27 := by
  change BiPoly.mul (h5e24.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p27
  rw [h5n24, h5n11]
  exact h5n27_arithmetic

#print axioms h5n27_arithmetic
end StackSorting.RationalLift
