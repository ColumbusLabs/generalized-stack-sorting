import Horner5Base
import Horner5Node063
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p64 : BiPoly.Poly := [[(Int.ofNat 192), (Int.ofNat 96)], [(Int.negSucc 287)]]

theorem h5n64_arithmetic : BiPoly.add h5p61 h5p63=h5p64 := by
  decide +kernel

theorem h5n64 : h5e64.toBi mapPolyEnv=h5p64 := by
  change BiPoly.add (h5e61.toBi mapPolyEnv) (h5e63.toBi mapPolyEnv)=h5p64
  rw [h5n61, h5n63]
  exact h5n64_arithmetic

#print axioms h5n64_arithmetic
end StackSorting.RationalLift
