import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p182 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 59)]]

theorem h5n182_arithmetic : BiPoly.mul h5p181 h5p11=h5p182 := by
  decide +kernel

theorem h5n182 : h5e182.toBi mapPolyEnv=h5p182 := by
  change BiPoly.mul (h5e181.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p182
  rw [h5n181, h5n11]
  exact h5n182_arithmetic

#print axioms h5n182_arithmetic
end StackSorting.RationalLift
