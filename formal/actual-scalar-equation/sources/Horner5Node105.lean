import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p105 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 53)]]

theorem h5n105_arithmetic : BiPoly.mul h5p104 h5p9=h5p105 := by
  decide +kernel

theorem h5n105 : h5e105.toBi mapPolyEnv=h5p105 := by
  change BiPoly.mul (h5e104.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p105
  rw [h5n104, h5n9]
  exact h5n105_arithmetic

#print axioms h5n105_arithmetic
end StackSorting.RationalLift
