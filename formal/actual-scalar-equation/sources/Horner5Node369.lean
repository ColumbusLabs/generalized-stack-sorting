import Horner5Base
import Horner5Node368
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p369 : BiPoly.Poly := [[(Int.negSucc 17), (Int.negSucc 17)], [(Int.ofNat 18)]]

theorem h5n369_arithmetic : BiPoly.add h5p155 h5p368=h5p369 := by
  decide +kernel

theorem h5n369 : h5e369.toBi mapPolyEnv=h5p369 := by
  change BiPoly.add (h5e155.toBi mapPolyEnv) (h5e368.toBi mapPolyEnv)=h5p369
  rw [h5n155, h5n368]
  exact h5n369_arithmetic

#print axioms h5n369_arithmetic
end StackSorting.RationalLift
