import Horner4Base
import Horner4Node197
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p198 : BiPoly.Poly := [[(Int.negSucc 31), (Int.ofNat 32)]]

theorem h4n198_arithmetic : BiPoly.add h4p195 h4p197=h4p198 := by
  decide +kernel

theorem h4n198 : h4e198.toBi mapPolyEnv=h4p198 := by
  change BiPoly.add (h4e195.toBi mapPolyEnv) (h4e197.toBi mapPolyEnv)=h4p198
  rw [h4n195, h4n197]
  exact h4n198_arithmetic

#print axioms h4n198_arithmetic
end StackSorting.RationalLift
