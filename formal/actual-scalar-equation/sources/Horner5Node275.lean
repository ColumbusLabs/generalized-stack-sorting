import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p275 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 8)]]

theorem h5n275_arithmetic : BiPoly.mul h5p274 h5p9=h5p275 := by
  decide +kernel

theorem h5n275 : h5e275.toBi mapPolyEnv=h5p275 := by
  change BiPoly.mul (h5e274.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p275
  rw [h5n274, h5n9]
  exact h5n275_arithmetic

#print axioms h5n275_arithmetic
end StackSorting.RationalLift
