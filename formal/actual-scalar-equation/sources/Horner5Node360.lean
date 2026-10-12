import Horner5Node093
import Horner5Node359
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p360 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 8)], [(Int.negSucc 23)]]

theorem h5n360_arithmetic : BiPoly.add h5p93 h5p359=h5p360 := by
  decide +kernel

theorem h5n360 : h5e360.toBi mapPolyEnv=h5p360 := by
  change BiPoly.add (h5e93.toBi mapPolyEnv) (h5e359.toBi mapPolyEnv)=h5p360
  rw [h5n93, h5n359]
  exact h5n360_arithmetic

#print axioms h5n360_arithmetic
end StackSorting.RationalLift
