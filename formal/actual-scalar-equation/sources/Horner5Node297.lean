import Horner5Base
import Horner5Node296
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p297 : BiPoly.Poly := [[(Int.ofNat 64), (Int.ofNat 32)], [(Int.negSucc 95)]]

theorem h5n297_arithmetic : BiPoly.add h5p294 h5p296=h5p297 := by
  decide +kernel

theorem h5n297 : h5e297.toBi mapPolyEnv=h5p297 := by
  change BiPoly.add (h5e294.toBi mapPolyEnv) (h5e296.toBi mapPolyEnv)=h5p297
  rw [h5n294, h5n296]
  exact h5n297_arithmetic

#print axioms h5n297_arithmetic
end StackSorting.RationalLift
