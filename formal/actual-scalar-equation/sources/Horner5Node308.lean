import Horner5Base
import Horner5Node060
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p308 : BiPoly.Poly := [[(Int.negSucc 47)], [(Int.ofNat 96)]]

theorem h5n308_arithmetic : BiPoly.add h5p94 h5p60=h5p308 := by
  decide +kernel

theorem h5n308 : h5e308.toBi mapPolyEnv=h5p308 := by
  change BiPoly.add (h5e94.toBi mapPolyEnv) (h5e60.toBi mapPolyEnv)=h5p308
  rw [h5n94, h5n60]
  exact h5n308_arithmetic

#print axioms h5n308_arithmetic
end StackSorting.RationalLift
