import Horner5Node128
import Horner5Node115
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p129 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 35)], [(Int.ofNat 36)]]

theorem h5n129_arithmetic : BiPoly.add h5p128 h5p115=h5p129 := by
  decide +kernel

theorem h5n129 : h5e129.toBi mapPolyEnv=h5p129 := by
  change BiPoly.add (h5e128.toBi mapPolyEnv) (h5e115.toBi mapPolyEnv)=h5p129
  rw [h5n128, h5n115]
  exact h5n129_arithmetic

#print axioms h5n129_arithmetic
end StackSorting.RationalLift
