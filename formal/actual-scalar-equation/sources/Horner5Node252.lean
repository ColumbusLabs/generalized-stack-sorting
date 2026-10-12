import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p252 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 35)]]

theorem h5n252_arithmetic : BiPoly.mul h5p113 h5p9=h5p252 := by
  decide +kernel

theorem h5n252 : h5e252.toBi mapPolyEnv=h5p252 := by
  change BiPoly.mul (h5e113.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p252
  rw [h5n113, h5n9]
  exact h5n252_arithmetic

#print axioms h5n252_arithmetic
end StackSorting.RationalLift
