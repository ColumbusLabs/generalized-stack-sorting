import Horner5Base
import Horner5Node010
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p344 : BiPoly.Poly := [[(Int.ofNat 48)], [(Int.negSucc 95)]]

theorem h5n344_arithmetic : BiPoly.add h5p191 h5p10=h5p344 := by
  decide +kernel

theorem h5n344 : h5e344.toBi mapPolyEnv=h5p344 := by
  change BiPoly.add (h5e191.toBi mapPolyEnv) (h5e10.toBi mapPolyEnv)=h5p344
  rw [h5n191, h5n10]
  exact h5n344_arithmetic

#print axioms h5n344_arithmetic
end StackSorting.RationalLift
