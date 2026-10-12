import Horner5Node060
import Horner5Node065
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p66 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 192), (Int.ofNat 96)], [(Int.ofNat 96), (Int.negSucc 287)]]

theorem h5n66_arithmetic : BiPoly.add h5p60 h5p65=h5p66 := by
  decide +kernel

theorem h5n66 : h5e66.toBi mapPolyEnv=h5p66 := by
  change BiPoly.add (h5e60.toBi mapPolyEnv) (h5e65.toBi mapPolyEnv)=h5p66
  rw [h5n60, h5n65]
  exact h5n66_arithmetic

#print axioms h5n66_arithmetic
end StackSorting.RationalLift
