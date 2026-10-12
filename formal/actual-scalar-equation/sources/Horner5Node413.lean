import Horner5Node410
import Horner5Node412
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p413 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 15), (Int.negSucc 31)], [(Int.ofNat 16)]]

theorem h5n413_arithmetic : BiPoly.add h5p410 h5p412=h5p413 := by
  decide +kernel

theorem h5n413 : h5e413.toBi mapPolyEnv=h5p413 := by
  change BiPoly.add (h5e410.toBi mapPolyEnv) (h5e412.toBi mapPolyEnv)=h5p413
  rw [h5n410, h5n412]
  exact h5n413_arithmetic

#print axioms h5n413_arithmetic
end StackSorting.RationalLift
