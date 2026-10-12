import Horner5Node336
import Horner5Node337
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p338 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 60)], [(Int.negSucc 59)]]

theorem h5n338_arithmetic : BiPoly.add h5p336 h5p337=h5p338 := by
  decide +kernel

theorem h5n338 : h5e338.toBi mapPolyEnv=h5p338 := by
  change BiPoly.add (h5e336.toBi mapPolyEnv) (h5e337.toBi mapPolyEnv)=h5p338
  rw [h5n336, h5n337]
  exact h5n338_arithmetic

#print axioms h5n338_arithmetic
end StackSorting.RationalLift
