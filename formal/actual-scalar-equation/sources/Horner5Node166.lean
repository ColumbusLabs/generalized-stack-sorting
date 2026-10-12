import Horner5Node128
import Horner5Node165
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p166 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 35)], [(Int.ofNat 12)]]

theorem h5n166_arithmetic : BiPoly.add h5p128 h5p165=h5p166 := by
  decide +kernel

theorem h5n166 : h5e166.toBi mapPolyEnv=h5p166 := by
  change BiPoly.add (h5e128.toBi mapPolyEnv) (h5e165.toBi mapPolyEnv)=h5p166
  rw [h5n128, h5n165]
  exact h5n166_arithmetic

#print axioms h5n166_arithmetic
end StackSorting.RationalLift
