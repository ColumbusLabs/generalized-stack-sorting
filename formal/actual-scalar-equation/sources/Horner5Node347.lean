import Horner5Base
import Horner5Node346
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p347 : BiPoly.Poly := [[(Int.negSucc 47), (Int.ofNat 48)], [(Int.ofNat 48), (Int.negSucc 95)]]

theorem h5n347_arithmetic : BiPoly.add h5p94 h5p346=h5p347 := by
  decide +kernel

theorem h5n347 : h5e347.toBi mapPolyEnv=h5p347 := by
  change BiPoly.add (h5e94.toBi mapPolyEnv) (h5e346.toBi mapPolyEnv)=h5p347
  rw [h5n94, h5n346]
  exact h5n347_arithmetic

#print axioms h5n347_arithmetic
end StackSorting.RationalLift
