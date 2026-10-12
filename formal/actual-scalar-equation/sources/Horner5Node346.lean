import Horner5Node318
import Horner5Node345
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p346 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 48)], [(Int.ofNat 48), (Int.negSucc 95)]]

theorem h5n346_arithmetic : BiPoly.add h5p318 h5p345=h5p346 := by
  decide +kernel

theorem h5n346 : h5e346.toBi mapPolyEnv=h5p346 := by
  change BiPoly.add (h5e318.toBi mapPolyEnv) (h5e345.toBi mapPolyEnv)=h5p346
  rw [h5n318, h5n345]
  exact h5n346_arithmetic

#print axioms h5n346_arithmetic
end StackSorting.RationalLift
