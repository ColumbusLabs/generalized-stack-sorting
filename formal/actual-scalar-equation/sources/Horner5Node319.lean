import Horner5Node317
import Horner5Node318
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p319 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 47)], [(Int.ofNat 48)]]

theorem h5n319_arithmetic : BiPoly.add h5p317 h5p318=h5p319 := by
  decide +kernel

theorem h5n319 : h5e319.toBi mapPolyEnv=h5p319 := by
  change BiPoly.add (h5e317.toBi mapPolyEnv) (h5e318.toBi mapPolyEnv)=h5p319
  rw [h5n317, h5n318]
  exact h5n319_arithmetic

#print axioms h5n319_arithmetic
end StackSorting.RationalLift
