import Horner4Base
import Horner4Node242
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p243 : BiPoly.Poly := [[(Int.ofNat 8), (Int.ofNat 16)]]

theorem h4n243_arithmetic : BiPoly.add h4p226 h4p242=h4p243 := by
  decide +kernel

theorem h4n243 : h4e243.toBi mapPolyEnv=h4p243 := by
  change BiPoly.add (h4e226.toBi mapPolyEnv) (h4e242.toBi mapPolyEnv)=h4p243
  rw [h4n226, h4n242]
  exact h4n243_arithmetic

#print axioms h4n243_arithmetic
end StackSorting.RationalLift
