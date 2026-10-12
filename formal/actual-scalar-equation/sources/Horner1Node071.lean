import Horner1Base
import Horner1Node060
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p71 : BiPoly.Poly := [[(Int.ofNat 16), (Int.ofNat 8)]]

theorem h1n71_arithmetic : BiPoly.add h1p70 h1p60=h1p71 := by
  decide +kernel

theorem h1n71 : h1e71.toBi mapPolyEnv=h1p71 := by
  change BiPoly.add (h1e70.toBi mapPolyEnv) (h1e60.toBi mapPolyEnv)=h1p71
  rw [h1n70, h1n60]
  exact h1n71_arithmetic

#print axioms h1n71_arithmetic
end StackSorting.RationalLift
