import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p226 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 216)]]

theorem h5n226_arithmetic : BiPoly.mul h5p206 h5p9=h5p226 := by
  decide +kernel

theorem h5n226 : h5e226.toBi mapPolyEnv=h5p226 := by
  change BiPoly.mul (h5e206.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p226
  rw [h5n206, h5n9]
  exact h5n226_arithmetic

#print axioms h5n226_arithmetic
end StackSorting.RationalLift
