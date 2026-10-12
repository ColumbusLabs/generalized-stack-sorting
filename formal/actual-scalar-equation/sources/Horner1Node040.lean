import Horner1Base
import Horner1Node039
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h1p40 : BiPoly.Poly := [[(Int.negSucc 11), (Int.negSucc 47)]]

theorem h1n40_arithmetic : BiPoly.add h1p37 h1p39=h1p40 := by
  decide +kernel

theorem h1n40 : h1e40.toBi mapPolyEnv=h1p40 := by
  change BiPoly.add (h1e37.toBi mapPolyEnv) (h1e39.toBi mapPolyEnv)=h1p40
  rw [h1n37, h1n39]
  exact h1n40_arithmetic

#print axioms h1n40_arithmetic
end StackSorting.RationalLift
