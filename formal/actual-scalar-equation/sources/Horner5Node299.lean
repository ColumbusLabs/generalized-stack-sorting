import Horner5Node293
import Horner5Node298
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p299 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 64), (Int.ofNat 32)], [(Int.ofNat 32), (Int.negSucc 95)]]

theorem h5n299_arithmetic : BiPoly.add h5p293 h5p298=h5p299 := by
  decide +kernel

theorem h5n299 : h5e299.toBi mapPolyEnv=h5p299 := by
  change BiPoly.add (h5e293.toBi mapPolyEnv) (h5e298.toBi mapPolyEnv)=h5p299
  rw [h5n293, h5n298]
  exact h5n299_arithmetic

#print axioms h5n299_arithmetic
end StackSorting.RationalLift
