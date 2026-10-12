import Horner5Node165
import Horner5Node168
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p169 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 23), (Int.negSucc 35)], [(Int.ofNat 12), (Int.ofNat 12)]]

theorem h5n169_arithmetic : BiPoly.add h5p165 h5p168=h5p169 := by
  decide +kernel

theorem h5n169 : h5e169.toBi mapPolyEnv=h5p169 := by
  change BiPoly.add (h5e165.toBi mapPolyEnv) (h5e168.toBi mapPolyEnv)=h5p169
  rw [h5n165, h5n168]
  exact h5n169_arithmetic

#print axioms h5n169_arithmetic
end StackSorting.RationalLift
