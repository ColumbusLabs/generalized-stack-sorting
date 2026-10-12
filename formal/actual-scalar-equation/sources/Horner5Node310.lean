import Horner5Node192
import Horner5Node309
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p310 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 47)], [(Int.negSucc 47), (Int.ofNat 96)]]

theorem h5n310_arithmetic : BiPoly.add h5p192 h5p309=h5p310 := by
  decide +kernel

theorem h5n310 : h5e310.toBi mapPolyEnv=h5p310 := by
  change BiPoly.add (h5e192.toBi mapPolyEnv) (h5e309.toBi mapPolyEnv)=h5p310
  rw [h5n192, h5n309]
  exact h5n310_arithmetic

#print axioms h5n310_arithmetic
end StackSorting.RationalLift
