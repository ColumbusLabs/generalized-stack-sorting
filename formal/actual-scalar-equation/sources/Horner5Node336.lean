import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p336 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 59)]]

theorem h5n336_arithmetic : BiPoly.mul h5p181 h5p9=h5p336 := by
  decide +kernel

theorem h5n336 : h5e336.toBi mapPolyEnv=h5p336 := by
  change BiPoly.mul (h5e181.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p336
  rw [h5n181, h5n9]
  exact h5n336_arithmetic

#print axioms h5n336_arithmetic
end StackSorting.RationalLift
