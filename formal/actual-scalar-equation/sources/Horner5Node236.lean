import Horner5Base
import Horner5Node235
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p236 : BiPoly.Poly := [[(Int.ofNat 144), (Int.ofNat 144), (Int.ofNat 288)], [(Int.negSucc 143)]]

theorem h5n236_arithmetic : BiPoly.add h5p36 h5p235=h5p236 := by
  decide +kernel

theorem h5n236 : h5e236.toBi mapPolyEnv=h5p236 := by
  change BiPoly.add (h5e36.toBi mapPolyEnv) (h5e235.toBi mapPolyEnv)=h5p236
  rw [h5n36, h5n235]
  exact h5n236_arithmetic

#print axioms h5n236_arithmetic
end StackSorting.RationalLift
