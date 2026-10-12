import Horner1Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p113 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 16)]]

theorem h1n113_arithmetic : BiPoly.mul h1p70 h1p9=h1p113 := by
  decide +kernel

theorem h1n113 : h1e113.toBi mapPolyEnv=h1p113 := by
  change BiPoly.mul (h1e70.toBi mapPolyEnv) (h1e9.toBi mapPolyEnv)=h1p113
  rw [h1n70, h1n9]
  exact h1n113_arithmetic

#print axioms h1n113_arithmetic
end StackSorting.RationalLift
