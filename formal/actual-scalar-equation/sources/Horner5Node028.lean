import Horner5Node026
import Horner5Node027
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p28 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 72)], [(Int.negSucc 71)]]

theorem h5n28_arithmetic : BiPoly.add h5p26 h5p27=h5p28 := by
  decide +kernel

theorem h5n28 : h5e28.toBi mapPolyEnv=h5p28 := by
  change BiPoly.add (h5e26.toBi mapPolyEnv) (h5e27.toBi mapPolyEnv)=h5p28
  rw [h5n26, h5n27]
  exact h5n28_arithmetic

#print axioms h5n28_arithmetic
end StackSorting.RationalLift
