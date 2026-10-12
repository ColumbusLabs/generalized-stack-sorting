import Horner5Base
import Horner5Node277
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p278 : BiPoly.Poly := [[(Int.ofNat 9), (Int.ofNat 9)], [(Int.negSucc 8)]]

theorem h5n278_arithmetic : BiPoly.add h5p273 h5p277=h5p278 := by
  decide +kernel

theorem h5n278 : h5e278.toBi mapPolyEnv=h5p278 := by
  change BiPoly.add (h5e273.toBi mapPolyEnv) (h5e277.toBi mapPolyEnv)=h5p278
  rw [h5n273, h5n277]
  exact h5n278_arithmetic

#print axioms h5n278_arithmetic
end StackSorting.RationalLift
