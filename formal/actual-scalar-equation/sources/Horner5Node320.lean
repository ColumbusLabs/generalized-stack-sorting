import Horner5Base
import Horner5Node319
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p320 : BiPoly.Poly := [[(Int.negSucc 47), (Int.negSucc 47)], [(Int.ofNat 48)]]

theorem h5n320_arithmetic : BiPoly.add h5p94 h5p319=h5p320 := by
  decide +kernel

theorem h5n320 : h5e320.toBi mapPolyEnv=h5p320 := by
  change BiPoly.add (h5e94.toBi mapPolyEnv) (h5e319.toBi mapPolyEnv)=h5p320
  rw [h5n94, h5n319]
  exact h5n320_arithmetic

#print axioms h5n320_arithmetic
end StackSorting.RationalLift
