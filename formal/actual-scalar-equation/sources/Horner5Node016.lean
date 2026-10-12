import Horner5Node013
import Horner5Node015
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p16 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 95)], [(Int.ofNat 288)]]

theorem h5n16_arithmetic : BiPoly.add h5p13 h5p15=h5p16 := by
  decide +kernel

theorem h5n16 : h5e16.toBi mapPolyEnv=h5p16 := by
  change BiPoly.add (h5e13.toBi mapPolyEnv) (h5e15.toBi mapPolyEnv)=h5p16
  rw [h5n13, h5n15]
  exact h5n16_arithmetic

#print axioms h5n16_arithmetic
end StackSorting.RationalLift
