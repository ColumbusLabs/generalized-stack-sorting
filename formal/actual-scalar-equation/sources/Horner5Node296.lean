import Horner5Node010
import Horner5Node295
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p296 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 32)], [(Int.negSucc 95)]]

theorem h5n296_arithmetic : BiPoly.add h5p10 h5p295=h5p296 := by
  decide +kernel

theorem h5n296 : h5e296.toBi mapPolyEnv=h5p296 := by
  change BiPoly.add (h5e10.toBi mapPolyEnv) (h5e295.toBi mapPolyEnv)=h5p296
  rw [h5n10, h5n295]
  exact h5n296_arithmetic

#print axioms h5n296_arithmetic
end StackSorting.RationalLift
