import Horner2Base
import Horner2Node073
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p74 : BiPoly.Poly := [[(Int.negSucc 1), (Int.negSucc 15)]]

theorem h2n74_arithmetic : BiPoly.add h2p71 h2p73=h2p74 := by
  decide +kernel

theorem h2n74 : h2e74.toBi mapPolyEnv=h2p74 := by
  change BiPoly.add (h2e71.toBi mapPolyEnv) (h2e73.toBi mapPolyEnv)=h2p74
  rw [h2n71, h2n73]
  exact h2n74_arithmetic

#print axioms h2n74_arithmetic
end StackSorting.RationalLift
