import Horner5Base
import Horner5Node255
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p256 : BiPoly.Poly := [[(Int.ofNat 36), (Int.ofNat 36), (Int.ofNat 72)], [(Int.negSucc 35)]]

theorem h5n256_arithmetic : BiPoly.add h5p114 h5p255=h5p256 := by
  decide +kernel

theorem h5n256 : h5e256.toBi mapPolyEnv=h5p256 := by
  change BiPoly.add (h5e114.toBi mapPolyEnv) (h5e255.toBi mapPolyEnv)=h5p256
  rw [h5n114, h5n255]
  exact h5n256_arithmetic

#print axioms h5n256_arithmetic
end StackSorting.RationalLift
