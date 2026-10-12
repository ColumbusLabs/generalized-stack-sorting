import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p49 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 143)]]

theorem h5n49_arithmetic : BiPoly.mul h5p35 h5p9=h5p49 := by
  decide +kernel

theorem h5n49 : h5e49.toBi mapPolyEnv=h5p49 := by
  change BiPoly.mul (h5e35.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p49
  rw [h5n35, h5n9]
  exact h5n49_arithmetic

#print axioms h5n49_arithmetic
end StackSorting.RationalLift
