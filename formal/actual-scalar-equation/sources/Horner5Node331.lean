import Horner5Base
import Horner5Node330
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p331 : BiPoly.Poly := [[(Int.negSucc 63), (Int.negSucc 31)], [(Int.ofNat 96)]]

theorem h5n331_arithmetic : BiPoly.add h5p328 h5p330=h5p331 := by
  decide +kernel

theorem h5n331 : h5e331.toBi mapPolyEnv=h5p331 := by
  change BiPoly.add (h5e328.toBi mapPolyEnv) (h5e330.toBi mapPolyEnv)=h5p331
  rw [h5n328, h5n330]
  exact h5n331_arithmetic

#print axioms h5n331_arithmetic
end StackSorting.RationalLift
