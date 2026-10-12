import Horner5Node393
import Horner5Node396
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p397 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 8), (Int.ofNat 16)], [(Int.negSucc 7)]]

theorem h5n397_arithmetic : BiPoly.add h5p393 h5p396=h5p397 := by
  decide +kernel

theorem h5n397 : h5e397.toBi mapPolyEnv=h5p397 := by
  change BiPoly.add (h5e393.toBi mapPolyEnv) (h5e396.toBi mapPolyEnv)=h5p397
  rw [h5n393, h5n396]
  exact h5n397_arithmetic

#print axioms h5n397_arithmetic
end StackSorting.RationalLift
