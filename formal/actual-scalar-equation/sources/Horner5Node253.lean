import Horner5Base
import Horner5Node027
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p253 : BiPoly.Poly := [[(Int.ofNat 36), (Int.ofNat 72)]]

theorem h5n253_arithmetic : BiPoly.add h5p114 h5p27=h5p253 := by
  decide +kernel

theorem h5n253 : h5e253.toBi mapPolyEnv=h5p253 := by
  change BiPoly.add (h5e114.toBi mapPolyEnv) (h5e27.toBi mapPolyEnv)=h5p253
  rw [h5n114, h5n27]
  exact h5n253_arithmetic

#print axioms h5n253_arithmetic
end StackSorting.RationalLift
