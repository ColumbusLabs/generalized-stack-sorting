import Horner4Base
import Horner4Node078
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p79 : BiPoly.Poly := [[(Int.ofNat 24), (Int.ofNat 24)]]

theorem h4n79_arithmetic : BiPoly.add h4p53 h4p78=h4p79 := by
  decide +kernel

theorem h4n79 : h4e79.toBi mapPolyEnv=h4p79 := by
  change BiPoly.add (h4e53.toBi mapPolyEnv) (h4e78.toBi mapPolyEnv)=h4p79
  rw [h4n53, h4n78]
  exact h4n79_arithmetic

#print axioms h4n79_arithmetic
end StackSorting.RationalLift
