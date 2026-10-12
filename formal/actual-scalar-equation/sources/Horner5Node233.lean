import Horner5Base
import Horner5Node232
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p233 : BiPoly.Poly := [[(Int.ofNat 144), (Int.ofNat 288)]]

theorem h5n233_arithmetic : BiPoly.add h5p36 h5p232=h5p233 := by
  decide +kernel

theorem h5n233 : h5e233.toBi mapPolyEnv=h5p233 := by
  change BiPoly.add (h5e36.toBi mapPolyEnv) (h5e232.toBi mapPolyEnv)=h5p233
  rw [h5n36, h5n232]
  exact h5n233_arithmetic

#print axioms h5n233_arithmetic
end StackSorting.RationalLift
