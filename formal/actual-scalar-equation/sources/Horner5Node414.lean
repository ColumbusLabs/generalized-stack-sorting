import Horner5Base
import Horner5Node413
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p414 : BiPoly.Poly := [[(Int.negSucc 15), (Int.negSucc 15), (Int.negSucc 31)], [(Int.ofNat 16)]]

theorem h5n414_arithmetic : BiPoly.add h5p409 h5p413=h5p414 := by
  decide +kernel

theorem h5n414 : h5e414.toBi mapPolyEnv=h5p414 := by
  change BiPoly.add (h5e409.toBi mapPolyEnv) (h5e413.toBi mapPolyEnv)=h5p414
  rw [h5n409, h5n413]
  exact h5n414_arithmetic

#print axioms h5n414_arithmetic
end StackSorting.RationalLift
