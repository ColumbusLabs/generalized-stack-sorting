import Horner5Node245
import Horner5Node246
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p247 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 53)], [(Int.ofNat 54)]]

theorem h5n247_arithmetic : BiPoly.add h5p245 h5p246=h5p247 := by
  decide +kernel

theorem h5n247 : h5e247.toBi mapPolyEnv=h5p247 := by
  change BiPoly.add (h5e245.toBi mapPolyEnv) (h5e246.toBi mapPolyEnv)=h5p247
  rw [h5n245, h5n246]
  exact h5n247_arithmetic

#print axioms h5n247_arithmetic
end StackSorting.RationalLift
