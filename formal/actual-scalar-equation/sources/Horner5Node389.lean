import Horner5Base
import Horner5Node388
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p389 : BiPoly.Poly := [[(Int.negSucc 11), (Int.negSucc 11)], [(Int.ofNat 12)]]

theorem h5n389_arithmetic : BiPoly.add h5p163 h5p388=h5p389 := by
  decide +kernel

theorem h5n389 : h5e389.toBi mapPolyEnv=h5p389 := by
  change BiPoly.add (h5e163.toBi mapPolyEnv) (h5e388.toBi mapPolyEnv)=h5p389
  rw [h5n163, h5n388]
  exact h5n389_arithmetic

#print axioms h5n389_arithmetic
end StackSorting.RationalLift
