import Horner5Node327
import Horner5Node332
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p333 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 63), (Int.negSucc 31)], [(Int.negSucc 31), (Int.ofNat 96)]]

theorem h5n333_arithmetic : BiPoly.add h5p327 h5p332=h5p333 := by
  decide +kernel

theorem h5n333 : h5e333.toBi mapPolyEnv=h5p333 := by
  change BiPoly.add (h5e327.toBi mapPolyEnv) (h5e332.toBi mapPolyEnv)=h5p333
  rw [h5n327, h5n332]
  exact h5n333_arithmetic

#print axioms h5n333_arithmetic
end StackSorting.RationalLift
