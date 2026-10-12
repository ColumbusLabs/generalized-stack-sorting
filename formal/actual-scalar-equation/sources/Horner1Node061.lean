import Horner1Base
import Horner1Node060
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p61 : BiPoly.Poly := [[(Int.ofNat 4), (Int.ofNat 8)]]

theorem h1n61_arithmetic : BiPoly.add h1p58 h1p60=h1p61 := by
  decide +kernel

theorem h1n61 : h1e61.toBi mapPolyEnv=h1p61 := by
  change BiPoly.add (h1e58.toBi mapPolyEnv) (h1e60.toBi mapPolyEnv)=h1p61
  rw [h1n58, h1n60]
  exact h1n61_arithmetic

#print axioms h1n61_arithmetic
end StackSorting.RationalLift
