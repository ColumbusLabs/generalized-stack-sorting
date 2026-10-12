import Horner5Node093
import Horner5Node099
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p100 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 47), (Int.negSucc 23)], [(Int.negSucc 23), (Int.ofNat 72)]]

theorem h5n100_arithmetic : BiPoly.add h5p93 h5p99=h5p100 := by
  decide +kernel

theorem h5n100 : h5e100.toBi mapPolyEnv=h5p100 := by
  change BiPoly.add (h5e93.toBi mapPolyEnv) (h5e99.toBi mapPolyEnv)=h5p100
  rw [h5n93, h5n99]
  exact h5n100_arithmetic

#print axioms h5n100_arithmetic
end StackSorting.RationalLift
