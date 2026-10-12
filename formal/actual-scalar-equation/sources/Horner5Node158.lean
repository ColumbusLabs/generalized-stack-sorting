import Horner5Node156
import Horner5Node157
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p158 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 18)], [(Int.negSucc 17)]]

theorem h5n158_arithmetic : BiPoly.add h5p156 h5p157=h5p158 := by
  decide +kernel

theorem h5n158 : h5e158.toBi mapPolyEnv=h5p158 := by
  change BiPoly.add (h5e156.toBi mapPolyEnv) (h5e157.toBi mapPolyEnv)=h5p158
  rw [h5n156, h5n157]
  exact h5n158_arithmetic

#print axioms h5n158_arithmetic
end StackSorting.RationalLift
