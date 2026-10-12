import Horner1Base
import Horner1Node010
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p11 : BiPoly.Poly := [[(Int.ofNat 24), (Int.ofNat 96)]]

theorem h1n11_arithmetic : BiPoly.add h1p7 h1p10=h1p11 := by
  decide +kernel

theorem h1n11 : h1e11.toBi mapPolyEnv=h1p11 := by
  change BiPoly.add (h1e7.toBi mapPolyEnv) (h1e10.toBi mapPolyEnv)=h1p11
  rw [h1n7, h1n10]
  exact h1n11_arithmetic

#print axioms h1n11_arithmetic
end StackSorting.RationalLift
