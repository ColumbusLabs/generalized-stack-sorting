import Horner5Node357
import Horner5Node362
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p363 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 16), (Int.ofNat 8)], [(Int.ofNat 8), (Int.negSucc 23)]]

theorem h5n363_arithmetic : BiPoly.add h5p357 h5p362=h5p363 := by
  decide +kernel

theorem h5n363 : h5e363.toBi mapPolyEnv=h5p363 := by
  change BiPoly.add (h5e357.toBi mapPolyEnv) (h5e362.toBi mapPolyEnv)=h5p363
  rw [h5n357, h5n362]
  exact h5n363_arithmetic

#print axioms h5n363_arithmetic
end StackSorting.RationalLift
