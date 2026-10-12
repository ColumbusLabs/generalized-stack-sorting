import Horner5Base
import Horner5Node397
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p398 : BiPoly.Poly := [[(Int.ofNat 8), (Int.ofNat 8), (Int.ofNat 16)], [(Int.negSucc 7)]]

theorem h5n398_arithmetic : BiPoly.add h5p356 h5p397=h5p398 := by
  decide +kernel

theorem h5n398 : h5e398.toBi mapPolyEnv=h5p398 := by
  change BiPoly.add (h5e356.toBi mapPolyEnv) (h5e397.toBi mapPolyEnv)=h5p398
  rw [h5n356, h5n397]
  exact h5n398_arithmetic

#print axioms h5n398_arithmetic
end StackSorting.RationalLift
