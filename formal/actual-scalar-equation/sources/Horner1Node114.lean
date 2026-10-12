import Horner1Base
import Horner1Node113
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p114 : BiPoly.Poly := [[(Int.ofNat 2), (Int.ofNat 16)]]

theorem h1n114_arithmetic : BiPoly.add h1p112 h1p113=h1p114 := by
  decide +kernel

theorem h1n114 : h1e114.toBi mapPolyEnv=h1p114 := by
  change BiPoly.add (h1e112.toBi mapPolyEnv) (h1e113.toBi mapPolyEnv)=h1p114
  rw [h1n112, h1n113]
  exact h1n114_arithmetic

#print axioms h1n114_arithmetic
end StackSorting.RationalLift
