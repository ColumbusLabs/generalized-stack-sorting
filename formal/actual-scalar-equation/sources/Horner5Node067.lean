import Horner5Base
import Horner5Node066
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p67 : BiPoly.Poly := [[(Int.negSucc 95), (Int.ofNat 192), (Int.ofNat 96)], [(Int.ofNat 96), (Int.negSucc 287)]]

theorem h5n67_arithmetic : BiPoly.add h5p8 h5p66=h5p67 := by
  decide +kernel

theorem h5n67 : h5e67.toBi mapPolyEnv=h5p67 := by
  change BiPoly.add (h5e8.toBi mapPolyEnv) (h5e66.toBi mapPolyEnv)=h5p67
  rw [h5n8, h5n66]
  exact h5n67_arithmetic

#print axioms h5n67_arithmetic
end StackSorting.RationalLift
