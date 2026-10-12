import Horner5Node070
import Horner5Node072
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p73 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 179)], [(Int.ofNat 180)]]

theorem h5n73_arithmetic : BiPoly.add h5p70 h5p72=h5p73 := by
  decide +kernel

theorem h5n73 : h5e73.toBi mapPolyEnv=h5p73 := by
  change BiPoly.add (h5e70.toBi mapPolyEnv) (h5e72.toBi mapPolyEnv)=h5p73
  rw [h5n70, h5n72]
  exact h5n73_arithmetic

#print axioms h5n73_arithmetic
end StackSorting.RationalLift
