import Horner5Base
import Horner5Node107
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p108 : BiPoly.Poly := [[(Int.ofNat 54), (Int.ofNat 54)], [(Int.negSucc 53)]]

theorem h5n108_arithmetic : BiPoly.add h5p103 h5p107=h5p108 := by
  decide +kernel

theorem h5n108 : h5e108.toBi mapPolyEnv=h5p108 := by
  change BiPoly.add (h5e103.toBi mapPolyEnv) (h5e107.toBi mapPolyEnv)=h5p108
  rw [h5n103, h5n107]
  exact h5n108_arithmetic

#print axioms h5n108_arithmetic
end StackSorting.RationalLift
