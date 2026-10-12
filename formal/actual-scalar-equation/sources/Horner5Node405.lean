import Horner5Base
import Horner5Node404
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p405 : BiPoly.Poly := [[(Int.ofNat 24), (Int.ofNat 24)], [(Int.negSucc 23)]]

theorem h5n405_arithmetic : BiPoly.add h5p91 h5p404=h5p405 := by
  decide +kernel

theorem h5n405 : h5e405.toBi mapPolyEnv=h5p405 := by
  change BiPoly.add (h5e91.toBi mapPolyEnv) (h5e404.toBi mapPolyEnv)=h5p405
  rw [h5n91, h5n404]
  exact h5n405_arithmetic

#print axioms h5n405_arithmetic
end StackSorting.RationalLift
