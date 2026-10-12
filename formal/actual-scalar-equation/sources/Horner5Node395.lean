import Horner5Base
import Horner5Node394
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p395 : BiPoly.Poly := [[(Int.ofNat 8), (Int.ofNat 16)]]

theorem h5n395_arithmetic : BiPoly.add h5p356 h5p394=h5p395 := by
  decide +kernel

theorem h5n395 : h5e395.toBi mapPolyEnv=h5p395 := by
  change BiPoly.add (h5e356.toBi mapPolyEnv) (h5e394.toBi mapPolyEnv)=h5p395
  rw [h5n356, h5n394]
  exact h5n395_arithmetic

#print axioms h5n395_arithmetic
end StackSorting.RationalLift
