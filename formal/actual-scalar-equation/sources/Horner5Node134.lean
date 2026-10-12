import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p134 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 24)]]

theorem h5n134_arithmetic : BiPoly.mul h5p91 h5p11=h5p134 := by
  decide +kernel

theorem h5n134 : h5e134.toBi mapPolyEnv=h5p134 := by
  change BiPoly.mul (h5e91.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p134
  rw [h5n91, h5n11]
  exact h5n134_arithmetic

#print axioms h5n134_arithmetic
end StackSorting.RationalLift
