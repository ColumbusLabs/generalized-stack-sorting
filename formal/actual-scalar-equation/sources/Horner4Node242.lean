import Horner4Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h4p242 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 16)]]

theorem h4n242_arithmetic : BiPoly.mul h4p241 h4p9=h4p242 := by
  decide +kernel

theorem h4n242 : h4e242.toBi mapPolyEnv=h4p242 := by
  change BiPoly.mul (h4e241.toBi mapPolyEnv) (h4e9.toBi mapPolyEnv)=h4p242
  rw [h4n241, h4n9]
  exact h4n242_arithmetic

#print axioms h4n242_arithmetic
end StackSorting.RationalLift
