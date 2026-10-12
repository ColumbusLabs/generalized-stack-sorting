import Horner4Base
import Horner4Node136
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p137 : BiPoly.Poly := [[(Int.negSucc 143), (Int.negSucc 287)]]

theorem h4n137_arithmetic : BiPoly.add h4p22 h4p136=h4p137 := by
  decide +kernel

theorem h4n137 : h4e137.toBi mapPolyEnv=h4p137 := by
  change BiPoly.add (h4e22.toBi mapPolyEnv) (h4e136.toBi mapPolyEnv)=h4p137
  rw [h4n22, h4n136]
  exact h4n137_arithmetic

#print axioms h4n137_arithmetic
end StackSorting.RationalLift
