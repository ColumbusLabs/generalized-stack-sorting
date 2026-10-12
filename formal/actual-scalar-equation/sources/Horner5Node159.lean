import Horner5Base
import Horner5Node158
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p159 : BiPoly.Poly := [[(Int.ofNat 18), (Int.ofNat 18)], [(Int.negSucc 17)]]

theorem h5n159_arithmetic : BiPoly.add h5p154 h5p158=h5p159 := by
  decide +kernel

theorem h5n159 : h5e159.toBi mapPolyEnv=h5p159 := by
  change BiPoly.add (h5e154.toBi mapPolyEnv) (h5e158.toBi mapPolyEnv)=h5p159
  rw [h5n154, h5n158]
  exact h5n159_arithmetic

#print axioms h5n159_arithmetic
end StackSorting.RationalLift
