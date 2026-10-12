import Horner5Base
import Horner5Node333
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p334 : BiPoly.Poly := [[(Int.ofNat 32), (Int.negSucc 63), (Int.negSucc 31)], [(Int.negSucc 31), (Int.ofNat 96)]]

theorem h5n334_arithmetic : BiPoly.add h5p292 h5p333=h5p334 := by
  decide +kernel

theorem h5n334 : h5e334.toBi mapPolyEnv=h5p334 := by
  change BiPoly.add (h5e292.toBi mapPolyEnv) (h5e333.toBi mapPolyEnv)=h5p334
  rw [h5n292, h5n333]
  exact h5n334_arithmetic

#print axioms h5n334_arithmetic
end StackSorting.RationalLift
