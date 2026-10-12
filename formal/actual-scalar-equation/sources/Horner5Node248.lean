import Horner5Base
import Horner5Node247
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p248 : BiPoly.Poly := [[(Int.negSucc 53), (Int.negSucc 53)], [(Int.ofNat 54)]]

theorem h5n248_arithmetic : BiPoly.add h5p104 h5p247=h5p248 := by
  decide +kernel

theorem h5n248 : h5e248.toBi mapPolyEnv=h5p248 := by
  change BiPoly.add (h5e104.toBi mapPolyEnv) (h5e247.toBi mapPolyEnv)=h5p248
  rw [h5n104, h5n247]
  exact h5n248_arithmetic

#print axioms h5n248_arithmetic
end StackSorting.RationalLift
