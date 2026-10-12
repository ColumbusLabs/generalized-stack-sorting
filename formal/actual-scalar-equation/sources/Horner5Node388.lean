import Horner5Node387
import Horner5Node165
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p388 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 11)], [(Int.ofNat 12)]]

theorem h5n388_arithmetic : BiPoly.add h5p387 h5p165=h5p388 := by
  decide +kernel

theorem h5n388 : h5e388.toBi mapPolyEnv=h5p388 := by
  change BiPoly.add (h5e387.toBi mapPolyEnv) (h5e165.toBi mapPolyEnv)=h5p388
  rw [h5n387, h5n165]
  exact h5n388_arithmetic

#print axioms h5n388_arithmetic
end StackSorting.RationalLift
