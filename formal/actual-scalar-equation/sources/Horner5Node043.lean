import Horner5Base
import Horner5Node042
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p43 : BiPoly.Poly := [[(Int.negSucc 143), (Int.ofNat 144)], [(Int.ofNat 144), (Int.negSucc 287)]]

theorem h5n43_arithmetic : BiPoly.add h5p35 h5p42=h5p43 := by
  decide +kernel

theorem h5n43 : h5e43.toBi mapPolyEnv=h5p43 := by
  change BiPoly.add (h5e35.toBi mapPolyEnv) (h5e42.toBi mapPolyEnv)=h5p43
  rw [h5n35, h5n42]
  exact h5n43_arithmetic

#print axioms h5n43_arithmetic
end StackSorting.RationalLift
