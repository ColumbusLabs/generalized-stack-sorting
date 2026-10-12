import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p245 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 53)]]

theorem h5n245_arithmetic : BiPoly.mul h5p104 h5p11=h5p245 := by
  decide +kernel

theorem h5n245 : h5e245.toBi mapPolyEnv=h5p245 := by
  change BiPoly.mul (h5e104.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p245
  rw [h5n104, h5n11]
  exact h5n245_arithmetic

#print axioms h5n245_arithmetic
end StackSorting.RationalLift
