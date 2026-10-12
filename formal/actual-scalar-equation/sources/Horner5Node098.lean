import Horner5Base
import Horner5Node097
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p98 : BiPoly.Poly := [[(Int.negSucc 47), (Int.negSucc 23)], [(Int.ofNat 72)]]

theorem h5n98_arithmetic : BiPoly.add h5p94 h5p97=h5p98 := by
  decide +kernel

theorem h5n98 : h5e98.toBi mapPolyEnv=h5p98 := by
  change BiPoly.add (h5e94.toBi mapPolyEnv) (h5e97.toBi mapPolyEnv)=h5p98
  rw [h5n94, h5n97]
  exact h5n98_arithmetic

#print axioms h5n98_arithmetic
end StackSorting.RationalLift
