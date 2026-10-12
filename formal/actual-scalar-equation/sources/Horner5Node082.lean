import Horner5Base
import Horner5Node081
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p82 : BiPoly.Poly := [[(Int.ofNat 144), (Int.negSucc 143)], [(Int.negSucc 143), (Int.ofNat 288)]]

theorem h5n82_arithmetic : BiPoly.add h5p36 h5p81=h5p82 := by
  decide +kernel

theorem h5n82 : h5e82.toBi mapPolyEnv=h5p82 := by
  change BiPoly.add (h5e36.toBi mapPolyEnv) (h5e81.toBi mapPolyEnv)=h5p82
  rw [h5n36, h5n81]
  exact h5n82_arithmetic

#print axioms h5n82_arithmetic
end StackSorting.RationalLift
