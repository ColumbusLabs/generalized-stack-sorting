import Horner5Node115
import Horner5Node117
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p118 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 36)], [(Int.ofNat 36), (Int.negSucc 71)]]

theorem h5n118_arithmetic : BiPoly.add h5p115 h5p117=h5p118 := by
  decide +kernel

theorem h5n118 : h5e118.toBi mapPolyEnv=h5p118 := by
  change BiPoly.add (h5e115.toBi mapPolyEnv) (h5e117.toBi mapPolyEnv)=h5p118
  rw [h5n115, h5n117]
  exact h5n118_arithmetic

#print axioms h5n118_arithmetic
end StackSorting.RationalLift
