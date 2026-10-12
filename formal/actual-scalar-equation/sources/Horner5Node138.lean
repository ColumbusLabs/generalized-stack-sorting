import Horner5Node093
import Horner5Node137
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p138 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 0), (Int.ofNat 24)], [(Int.negSucc 23), (Int.ofNat 24)]]

theorem h5n138_arithmetic : BiPoly.add h5p93 h5p137=h5p138 := by
  decide +kernel

theorem h5n138 : h5e138.toBi mapPolyEnv=h5p138 := by
  change BiPoly.add (h5e93.toBi mapPolyEnv) (h5e137.toBi mapPolyEnv)=h5p138
  rw [h5n93, h5n137]
  exact h5n138_arithmetic

#print axioms h5n138_arithmetic
end StackSorting.RationalLift
