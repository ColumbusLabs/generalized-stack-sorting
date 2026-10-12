import Horner5Node252
import Horner5Node254
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p255 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 36), (Int.ofNat 72)], [(Int.negSucc 35)]]

theorem h5n255_arithmetic : BiPoly.add h5p252 h5p254=h5p255 := by
  decide +kernel

theorem h5n255 : h5e255.toBi mapPolyEnv=h5p255 := by
  change BiPoly.add (h5e252.toBi mapPolyEnv) (h5e254.toBi mapPolyEnv)=h5p255
  rw [h5n252, h5n254]
  exact h5n255_arithmetic

#print axioms h5n255_arithmetic
end StackSorting.RationalLift
