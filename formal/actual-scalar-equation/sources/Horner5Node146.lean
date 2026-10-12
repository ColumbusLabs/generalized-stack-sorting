import Horner5Base
import Horner5Node145
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p146 : BiPoly.Poly := [[(Int.ofNat 96), (Int.ofNat 96)], [(Int.negSucc 95)]]

theorem h5n146_arithmetic : BiPoly.add h5p7 h5p145=h5p146 := by
  decide +kernel

theorem h5n146 : h5e146.toBi mapPolyEnv=h5p146 := by
  change BiPoly.add (h5e7.toBi mapPolyEnv) (h5e145.toBi mapPolyEnv)=h5p146
  rw [h5n7, h5n145]
  exact h5n146_arithmetic

#print axioms h5n146_arithmetic
end StackSorting.RationalLift
