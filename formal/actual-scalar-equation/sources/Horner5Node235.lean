import Horner5Node049
import Horner5Node234
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p235 : BiPoly.Poly := [[(Int.ofNat 0), (Int.ofNat 144), (Int.ofNat 288)], [(Int.negSucc 143)]]

theorem h5n235_arithmetic : BiPoly.add h5p49 h5p234=h5p235 := by
  decide +kernel

theorem h5n235 : h5e235.toBi mapPolyEnv=h5p235 := by
  change BiPoly.add (h5e49.toBi mapPolyEnv) (h5e234.toBi mapPolyEnv)=h5p235
  rw [h5n49, h5n234]
  exact h5n235_arithmetic

#print axioms h5n235_arithmetic
end StackSorting.RationalLift
