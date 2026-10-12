import Horner4Base
import Horner4Node104
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p105 : BiPoly.Poly := [[(Int.negSucc 11), (Int.negSucc 35)]]

theorem h4n105_arithmetic : BiPoly.add h4p103 h4p104=h4p105 := by
  decide +kernel

theorem h4n105 : h4e105.toBi mapPolyEnv=h4p105 := by
  change BiPoly.add (h4e103.toBi mapPolyEnv) (h4e104.toBi mapPolyEnv)=h4p105
  rw [h4n103, h4n104]
  exact h4n105_arithmetic

#print axioms h4n105_arithmetic
end StackSorting.RationalLift
