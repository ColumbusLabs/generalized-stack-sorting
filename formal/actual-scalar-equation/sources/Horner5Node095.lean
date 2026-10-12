import Horner5Base
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p95 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 23)]]

theorem h5n95_arithmetic : BiPoly.mul h5p92 h5p11=h5p95 := by
  decide +kernel

theorem h5n95 : h5e95.toBi mapPolyEnv=h5p95 := by
  change BiPoly.mul (h5e92.toBi mapPolyEnv) (h5e11.toBi mapPolyEnv)=h5p95
  rw [h5n92, h5n11]
  exact h5n95_arithmetic

#print axioms h5n95_arithmetic
end StackSorting.RationalLift
