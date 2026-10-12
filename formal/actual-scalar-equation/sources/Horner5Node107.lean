import Horner5Node105
import Horner5Node106
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p107 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 54)], [(Int.negSucc 53)]]

theorem h5n107_arithmetic : BiPoly.add h5p105 h5p106=h5p107 := by
  decide +kernel

theorem h5n107 : h5e107.toBi mapPolyEnv=h5p107 := by
  change BiPoly.add (h5e105.toBi mapPolyEnv) (h5e106.toBi mapPolyEnv)=h5p107
  rw [h5n105, h5n106]
  exact h5n107_arithmetic

#print axioms h5n107_arithmetic
end StackSorting.RationalLift
