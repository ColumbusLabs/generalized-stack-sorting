import Horner0Base
import Horner0Node077
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h0p78 : BiPoly.Poly := [[(Int.negSucc 11), (Int.negSucc 23)]]

theorem h0n78_arithmetic : BiPoly.add h0p37 h0p77=h0p78 := by
  decide +kernel

theorem h0n78 : h0e78.toBi mapPolyEnv=h0p78 := by
  change BiPoly.add (h0e37.toBi mapPolyEnv) (h0e77.toBi mapPolyEnv)=h0p78
  rw [h0n37, h0n77]
  exact h0n78_arithmetic

#print axioms h0n78_arithmetic
end StackSorting.RationalLift
