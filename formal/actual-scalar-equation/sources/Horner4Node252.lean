import Horner4Base
import Horner4Node212
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p252 : BiPoly.Poly := [[(Int.negSucc 15), (Int.negSucc 31)]]

theorem h4n252_arithmetic : BiPoly.add h4p251 h4p212=h4p252 := by
  decide +kernel

theorem h4n252 : h4e252.toBi mapPolyEnv=h4p252 := by
  change BiPoly.add (h4e251.toBi mapPolyEnv) (h4e212.toBi mapPolyEnv)=h4p252
  rw [h4n251, h4n212]
  exact h4n252_arithmetic

#print axioms h4n252_arithmetic
end StackSorting.RationalLift
