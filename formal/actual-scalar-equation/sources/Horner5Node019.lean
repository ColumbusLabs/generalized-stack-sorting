import Horner5Node010
import Horner5Node018
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p19 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 191), (Int.negSucc 95)], [(Int.negSucc 95), (Int.ofNat 288)]]

theorem h5n19_arithmetic : BiPoly.add h5p10 h5p18=h5p19 := by
  decide +kernel

theorem h5n19 : h5e19.toBi mapPolyEnv=h5p19 := by
  change BiPoly.add (h5e10.toBi mapPolyEnv) (h5e18.toBi mapPolyEnv)=h5p19
  rw [h5n10, h5n18]
  exact h5n19_arithmetic

#print axioms h5n19_arithmetic
end StackSorting.RationalLift
