import Horner5Base
import Horner5Node302
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p303 : BiPoly.Poly := [[(Int.negSucc 23), (Int.negSucc 23)], [(Int.ofNat 24)]]

theorem h5n303_arithmetic : BiPoly.add h5p92 h5p302=h5p303 := by
  decide +kernel

theorem h5n303 : h5e303.toBi mapPolyEnv=h5p303 := by
  change BiPoly.add (h5e92.toBi mapPolyEnv) (h5e302.toBi mapPolyEnv)=h5p303
  rw [h5n92, h5n302]
  exact h5n303_arithmetic

#print axioms h5n303_arithmetic
end StackSorting.RationalLift
