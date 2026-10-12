import Horner5Base
import Horner5Node015
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p79 : BiPoly.Poly := [[(Int.negSucc 143)], [(Int.ofNat 288)]]

theorem h5n79_arithmetic : BiPoly.add h5p35 h5p15=h5p79 := by
  decide +kernel

theorem h5n79 : h5e79.toBi mapPolyEnv=h5p79 := by
  change BiPoly.add (h5e35.toBi mapPolyEnv) (h5e15.toBi mapPolyEnv)=h5p79
  rw [h5n35, h5n15]
  exact h5n79_arithmetic

#print axioms h5n79_arithmetic
end StackSorting.RationalLift
