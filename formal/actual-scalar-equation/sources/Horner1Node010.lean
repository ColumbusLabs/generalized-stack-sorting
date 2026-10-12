import Horner1Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p10 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 96)]]

theorem h1n10_arithmetic : BiPoly.mul h1p8 h1p9=h1p10 := by
  decide +kernel

theorem h1n10 : h1e10.toBi mapPolyEnv=h1p10 := by
  change BiPoly.mul (h1e8.toBi mapPolyEnv) (h1e9.toBi mapPolyEnv)=h1p10
  rw [h1n8, h1n9]
  exact h1n10_arithmetic

#print axioms h1n10_arithmetic
end StackSorting.RationalLift
