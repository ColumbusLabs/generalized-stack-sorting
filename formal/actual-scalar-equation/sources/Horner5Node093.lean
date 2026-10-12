import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p93 : BiPoly.Poly := [[(Int.ofNat 0)], [(Int.negSucc 23)]]

theorem h5n93_arithmetic : BiPoly.mul h5p92 h5p9=h5p93 := by
  decide +kernel

theorem h5n93 : h5e93.toBi mapPolyEnv=h5p93 := by
  change BiPoly.mul (h5e92.toBi mapPolyEnv) (h5e9.toBi mapPolyEnv)=h5p93
  rw [h5n92, h5n9]
  exact h5n93_arithmetic

#print axioms h5n93_arithmetic
end StackSorting.RationalLift
