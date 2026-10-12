import Horner5Node275
import Horner5Node276
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p277 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 9)], [(Int.negSucc 8)]]

theorem h5n277_arithmetic : BiPoly.add h5p275 h5p276=h5p277 := by
  decide +kernel

theorem h5n277 : h5e277.toBi mapPolyEnv=h5p277 := by
  change BiPoly.add (h5e275.toBi mapPolyEnv) (h5e276.toBi mapPolyEnv)=h5p277
  rw [h5n275, h5n276]
  exact h5n277_arithmetic

#print axioms h5n277_arithmetic
end StackSorting.RationalLift
