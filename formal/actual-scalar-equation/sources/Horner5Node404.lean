import Horner5Node093
import Horner5Node134
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p404 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 24)], [(Int.negSucc 23)]]

theorem h5n404_arithmetic : BiPoly.add h5p93 h5p134=h5p404 := by
  decide +kernel

theorem h5n404 : h5e404.toBi mapPolyEnv=h5p404 := by
  change BiPoly.add (h5e93.toBi mapPolyEnv) (h5e134.toBi mapPolyEnv)=h5p404
  rw [h5n93, h5n134]
  exact h5n404_arithmetic

#print axioms h5n404_arithmetic
end StackSorting.RationalLift
