import Horner5Base
import Horner5Node215
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p216 : BiPoly.Poly := [[(Int.negSucc 143), (Int.negSucc 287)]]

theorem h5n216_arithmetic : BiPoly.add h5p35 h5p215=h5p216 := by
  decide +kernel

theorem h5n216 : h5e216.toBi mapPolyEnv=h5p216 := by
  change BiPoly.add (h5e35.toBi mapPolyEnv) (h5e215.toBi mapPolyEnv)=h5p216
  rw [h5n35, h5n215]
  exact h5n216_arithmetic

#print axioms h5n216_arithmetic
end StackSorting.RationalLift
