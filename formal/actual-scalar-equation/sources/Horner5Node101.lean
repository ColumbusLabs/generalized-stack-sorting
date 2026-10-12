import Horner5Base
import Horner5Node100
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p101 : BiPoly.Poly := [[(Int.ofNat 24), (Int.negSucc 47), (Int.negSucc 23)], [(Int.negSucc 23), (Int.ofNat 72)]]

theorem h5n101_arithmetic : BiPoly.add h5p91 h5p100=h5p101 := by
  decide +kernel

theorem h5n101 : h5e101.toBi mapPolyEnv=h5p101 := by
  change BiPoly.add (h5e91.toBi mapPolyEnv) (h5e100.toBi mapPolyEnv)=h5p101
  rw [h5n91, h5n100]
  exact h5n101_arithmetic

#print axioms h5n101_arithmetic
end StackSorting.RationalLift
