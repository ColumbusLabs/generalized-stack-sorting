import Horner4Base
import Horner4Node160
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p161 : BiPoly.Poly := [[(Int.ofNat 36), (Int.ofNat 72)]]

theorem h4n161_arithmetic : BiPoly.add h4p97 h4p160=h4p161 := by
  decide +kernel

theorem h4n161 : h4e161.toBi mapPolyEnv=h4p161 := by
  change BiPoly.add (h4e97.toBi mapPolyEnv) (h4e160.toBi mapPolyEnv)=h4p161
  rw [h4n97, h4n160]
  exact h4n161_arithmetic

#print axioms h4n161_arithmetic
end StackSorting.RationalLift
