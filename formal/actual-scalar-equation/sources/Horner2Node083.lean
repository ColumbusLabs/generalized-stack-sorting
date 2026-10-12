import Horner2Base
import Horner2Node082
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h2p83 : BiPoly.Poly := [[(Int.ofNat 4), (Int.ofNat 32)]]

theorem h2n83_arithmetic : BiPoly.add h2p51 h2p82=h2p83 := by
  decide +kernel

theorem h2n83 : h2e83.toBi mapPolyEnv=h2p83 := by
  change BiPoly.add (h2e51.toBi mapPolyEnv) (h2e82.toBi mapPolyEnv)=h2p83
  rw [h2n51, h2n82]
  exact h2n83_arithmetic

#print axioms h2n83_arithmetic
end StackSorting.RationalLift
