import Horner2Base
import Horner2Node023
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p24 : BiPoly.Poly := [[(Int.negSucc 23), (Int.negSucc 95)]]

theorem h2n24_arithmetic : BiPoly.add h2p21 h2p23=h2p24 := by
  decide +kernel

theorem h2n24 : h2e24.toBi mapPolyEnv=h2p24 := by
  change BiPoly.add (h2e21.toBi mapPolyEnv) (h2e23.toBi mapPolyEnv)=h2p24
  rw [h2n21, h2n23]
  exact h2n24_arithmetic

#print axioms h2n24_arithmetic
end StackSorting.RationalLift
