import Horner5Node329
import Horner5Node060
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p330 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 31)], [(Int.ofNat 96)]]

theorem h5n330_arithmetic : BiPoly.add h5p329 h5p60=h5p330 := by
  decide +kernel

theorem h5n330 : h5e330.toBi mapPolyEnv=h5p330 := by
  change BiPoly.add (h5e329.toBi mapPolyEnv) (h5e60.toBi mapPolyEnv)=h5p330
  rw [h5n329, h5n60]
  exact h5n330_arithmetic

#print axioms h5n330_arithmetic
end StackSorting.RationalLift
