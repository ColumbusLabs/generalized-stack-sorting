import Horner5Node208
import Horner5Node209
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p210 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 216)], [(Int.negSucc 215)]]

theorem h5n210_arithmetic : BiPoly.add h5p208 h5p209=h5p210 := by
  decide +kernel

theorem h5n210 : h5e210.toBi mapPolyEnv=h5p210 := by
  change BiPoly.add (h5e208.toBi mapPolyEnv) (h5e209.toBi mapPolyEnv)=h5p210
  rw [h5n208, h5n209]
  exact h5n210_arithmetic

#print axioms h5n210_arithmetic
end StackSorting.RationalLift
