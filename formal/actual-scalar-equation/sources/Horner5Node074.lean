import Horner5Base
import Horner5Node073
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p74 : BiPoly.Poly := [[(Int.negSucc 179), (Int.negSucc 179)], [(Int.ofNat 180)]]

theorem h5n74_arithmetic : BiPoly.add h5p69 h5p73=h5p74 := by
  decide +kernel

theorem h5n74 : h5e74.toBi mapPolyEnv=h5p74 := by
  change BiPoly.add (h5e69.toBi mapPolyEnv) (h5e73.toBi mapPolyEnv)=h5p74
  rw [h5n69, h5n73]
  exact h5n74_arithmetic

#print axioms h5n74_arithmetic
end StackSorting.RationalLift
