import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p193 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 48)]]

theorem h5n193_arithmetic : BiPoly.mul h5p191 h5p11=h5p193 := by
  decide +kernel

theorem h5n193 : h5e193.toBi mapPolyEnv=h5p193 := by
  change BiPoly.mul (h5e191.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p193
  rw [h5n191, h5n11]
  exact h5n193_arithmetic

#print axioms h5n193_arithmetic
end StackSorting.RationalLift
