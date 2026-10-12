import Horner5Node049
import Horner5Node080
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p81 : BiPoly.Poly := [[(Int.ofNat 0), (Int.negSucc 143)], [(Int.negSucc 143), (Int.ofNat 288)]]

theorem h5n81_arithmetic : BiPoly.add h5p49 h5p80=h5p81 := by
  decide +kernel

theorem h5n81 : h5e81.toBi mapPolyEnv=h5p81 := by
  change BiPoly.add (h5e49.toBi mapPolyEnv) (h5e80.toBi mapPolyEnv)=h5p81
  rw [h5n49, h5n80]
  exact h5n81_arithmetic

#print axioms h5n81_arithmetic
end StackSorting.RationalLift
