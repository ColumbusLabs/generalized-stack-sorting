import Horner5Base
import Horner5Node210
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p211 : BiPoly.Poly := [[(Int.ofNat 216), (Int.ofNat 216)], [(Int.negSucc 215)]]

theorem h5n211_arithmetic : BiPoly.add h5p206 h5p210=h5p211 := by
  decide +kernel

theorem h5n211 : h5e211.toBi mapPolyEnv=h5p211 := by
  change BiPoly.add (h5e206.toBi mapPolyEnv) (h5e210.toBi mapPolyEnv)=h5p211
  rw [h5n206, h5n210]
  exact h5n211_arithmetic

#print axioms h5n211_arithmetic
end StackSorting.RationalLift
