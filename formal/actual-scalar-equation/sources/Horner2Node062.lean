import Horner2Base
import Horner2Node061
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p62 : BiPoly.Poly := [[(Int.negSucc 11), (Int.negSucc 11)]]

theorem h2n62_arithmetic : BiPoly.add h2p49 h2p61=h2p62 := by
  decide +kernel

theorem h2n62 : h2e62.toBi mapPolyEnv=h2p62 := by
  change BiPoly.add (h2e49.toBi mapPolyEnv) (h2e61.toBi mapPolyEnv)=h2p62
  rw [h2n49, h2n61]
  exact h2n62_arithmetic

#print axioms h2n62_arithmetic
end StackSorting.RationalLift
