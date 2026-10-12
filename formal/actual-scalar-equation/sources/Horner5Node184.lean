import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p184 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 60)]]

theorem h5n184_arithmetic : BiPoly.mul h5p183 h5p9=h5p184 := by
  decide +kernel

theorem h5n184 : h5e184.toBi mapPolyEnv=h5p184 := by
  change BiPoly.mul (h5e183.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p184
  rw [h5n183, h5n9]
  exact h5n184_arithmetic

#print axioms h5n184_arithmetic
end StackSorting.RationalLift
