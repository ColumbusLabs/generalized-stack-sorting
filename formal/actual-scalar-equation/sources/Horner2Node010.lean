import Horner2Base
import Horner2Node009
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p10 : BiPoly.Poly := [[(Int.ofNat 12), (Int.ofNat 48)]]

theorem h2n10_arithmetic : BiPoly.add h2p6 h2p9=h2p10 := by
  decide +kernel

theorem h2n10 : h2e10.toBi mapPolyEnv=h2p10 := by
  change BiPoly.add (h2e6.toBi mapPolyEnv) (h2e9.toBi mapPolyEnv)=h2p10
  rw [h2n6, h2n9]
  exact h2n10_arithmetic

#print axioms h2n10_arithmetic
end StackSorting.RationalLift
