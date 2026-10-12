import Horner4Base
import Horner4Node055
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p56 : BiPoly.Poly := [[(Int.ofNat 24), (Int.negSucc 23)]]

theorem h4n56_arithmetic : BiPoly.add h4p53 h4p55=h4p56 := by
  decide +kernel

theorem h4n56 : h4e56.toBi mapPolyEnv=h4p56 := by
  change BiPoly.add (h4e53.toBi mapPolyEnv) (h4e55.toBi mapPolyEnv)=h4p56
  rw [h4n53, h4n55]
  exact h4n56_arithmetic

#print axioms h4n56_arithmetic
end StackSorting.RationalLift
