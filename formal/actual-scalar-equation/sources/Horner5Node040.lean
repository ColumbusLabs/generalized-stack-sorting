import Horner5Base
import Horner5Node039
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p40 : BiPoly.Poly := [[(Int.ofNat 144)], [(Int.negSucc 287)]]

theorem h5n40_arithmetic : BiPoly.add h5p36 h5p39=h5p40 := by
  decide +kernel

theorem h5n40 : h5e40.toBi mapPolyEnv=h5p40 := by
  change BiPoly.add (h5e36.toBi mapPolyEnv) (h5e39.toBi mapPolyEnv)=h5p40
  rw [h5n36, h5n39]
  exact h5n40_arithmetic

#print axioms h5n40_arithmetic
end StackSorting.RationalLift
