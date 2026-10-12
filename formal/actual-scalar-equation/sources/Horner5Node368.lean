import Horner5Node366
import Horner5Node367
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p368 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 17)], [(Int.ofNat 18)]]

theorem h5n368_arithmetic : BiPoly.add h5p366 h5p367=h5p368 := by
  decide +kernel

theorem h5n368 : h5e368.toBi mapPolyEnv=h5p368 := by
  change BiPoly.add (h5e366.toBi mapPolyEnv) (h5e367.toBi mapPolyEnv)=h5p368
  rw [h5n366, h5n367]
  exact h5n368_arithmetic

#print axioms h5n368_arithmetic
end StackSorting.RationalLift
