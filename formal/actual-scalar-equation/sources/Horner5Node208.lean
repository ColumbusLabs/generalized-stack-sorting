import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p208 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 215)]]

theorem h5n208_arithmetic : BiPoly.mul h5p207 h5p9=h5p208 := by
  decide +kernel

theorem h5n208 : h5e208.toBi mapPolyEnv=h5p208 := by
  change BiPoly.mul (h5e207.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p208
  rw [h5n207, h5n9]
  exact h5n208_arithmetic

#print axioms h5n208_arithmetic
end StackSorting.RationalLift
