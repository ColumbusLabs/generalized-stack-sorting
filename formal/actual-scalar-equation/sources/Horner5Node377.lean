import Horner5Node374
import Horner5Node376
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p377 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 11)], [(Int.negSucc 11), (Int.ofNat 24)]]

theorem h5n377_arithmetic : BiPoly.add h5p374 h5p376=h5p377 := by
  decide +kernel

theorem h5n377 : h5e377.toBi mapPolyEnv=h5p377 := by
  change BiPoly.add (h5e374.toBi mapPolyEnv) (h5e376.toBi mapPolyEnv)=h5p377
  rw [h5n374, h5n376]
  exact h5n377_arithmetic

#print axioms h5n377_arithmetic
end StackSorting.RationalLift
