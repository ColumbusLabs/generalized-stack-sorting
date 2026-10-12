import Horner4Base
import Horner4Node212
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p213 : BiPoly.Poly := [[(Int.ofNat 32), (Int.negSucc 31)]]

theorem h4n213_arithmetic : BiPoly.add h4p196 h4p212=h4p213 := by
  decide +kernel

theorem h4n213 : h4e213.toBi mapPolyEnv=h4p213 := by
  change BiPoly.add (h4e196.toBi mapPolyEnv) (h4e212.toBi mapPolyEnv)=h4p213
  rw [h4n196, h4n212]
  exact h4n213_arithmetic

#print axioms h4n213_arithmetic
end StackSorting.RationalLift
