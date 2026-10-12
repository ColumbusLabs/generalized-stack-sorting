import Horner5Base
import Horner5Node169
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p170 : BiPoly.Poly := [[(Int.negSucc 11), (Int.negSucc 23), (Int.negSucc 35)], [(Int.ofNat 12), (Int.ofNat 12)]]

theorem h5n170_arithmetic : BiPoly.add h5p163 h5p169=h5p170 := by
  decide +kernel

theorem h5n170 : h5e170.toBi mapPolyEnv=h5p170 := by
  change BiPoly.add (h5e163.toBi mapPolyEnv) (h5e169.toBi mapPolyEnv)=h5p170
  rw [h5n163, h5n169]
  exact h5n170_arithmetic

#print axioms h5n170_arithmetic
end StackSorting.RationalLift
