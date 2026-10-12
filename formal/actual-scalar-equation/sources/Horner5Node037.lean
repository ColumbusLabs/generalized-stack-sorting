import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p37 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.ofNat 144)]]

theorem h5n37_arithmetic : BiPoly.mul h5p36 h5p9=h5p37 := by
  decide +kernel

theorem h5n37 : h5e37.toBi mapPolyEnv=h5p37 := by
  change BiPoly.mul (h5e36.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p37
  rw [h5n36, h5n9]
  exact h5n37_arithmetic

#print axioms h5n37_arithmetic
end StackSorting.RationalLift
