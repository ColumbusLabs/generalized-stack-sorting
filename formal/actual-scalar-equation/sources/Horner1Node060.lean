import Horner1Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p60 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 8)]]

theorem h1n60_arithmetic : BiPoly.mul h1p59 h1p9=h1p60 := by
  decide +kernel

theorem h1n60 : h1e60.toBi mapPolyEnv=h1p60 := by
  change BiPoly.mul (h1e59.toBi mapPolyEnv) (h1e9.toBi mapPolyEnv)=h1p60
  rw [h1n59, h1n9]
  exact h1n60_arithmetic

#print axioms h1n60_arithmetic
end StackSorting.RationalLift
