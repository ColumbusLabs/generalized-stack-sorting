import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p50 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 144)]]

theorem h5n50_arithmetic : BiPoly.mul h5p36 h5p11=h5p50 := by
  decide +kernel

theorem h5n50 : h5e50.toBi mapPolyEnv=h5p50 := by
  change BiPoly.mul (h5e36.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p50
  rw [h5n36, h5n11]
  exact h5n50_arithmetic

#print axioms h5n50_arithmetic
end StackSorting.RationalLift
