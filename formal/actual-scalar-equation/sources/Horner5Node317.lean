import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p317 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 47)]]

theorem h5n317_arithmetic : BiPoly.mul h5p94 h5p11=h5p317 := by
  decide +kernel

theorem h5n317 : h5e317.toBi mapPolyEnv=h5p317 := by
  change BiPoly.mul (h5e94.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p317
  rw [h5n94, h5n11]
  exact h5n317_arithmetic

#print axioms h5n317_arithmetic
end StackSorting.RationalLift
