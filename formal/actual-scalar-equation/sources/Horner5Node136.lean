import Horner5Node134
import Horner5Node135
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p136 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 24)], [(Int.ofNat 24)]]

theorem h5n136_arithmetic : BiPoly.add h5p134 h5p135=h5p136 := by
  decide +kernel

theorem h5n136 : h5e136.toBi mapPolyEnv=h5p136 := by
  change BiPoly.add (h5e134.toBi mapPolyEnv) (h5e135.toBi mapPolyEnv)=h5p136
  rw [h5n134, h5n135]
  exact h5n136_arithmetic

#print axioms h5n136_arithmetic
end StackSorting.RationalLift
