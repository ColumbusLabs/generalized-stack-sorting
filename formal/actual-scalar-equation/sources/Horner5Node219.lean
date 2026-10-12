import Horner5Base
import Horner5Node218
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p219 : BiPoly.Poly := [[(Int.negSucc 143), (Int.negSucc 143), (Int.negSucc 287)], [(Int.ofNat 144)]]

theorem h5n219_arithmetic : BiPoly.add h5p35 h5p218=h5p219 := by
  decide +kernel

theorem h5n219 : h5e219.toBi mapPolyEnv=h5p219 := by
  change BiPoly.add (h5e35.toBi mapPolyEnv) (h5e218.toBi mapPolyEnv)=h5p219
  rw [h5n35, h5n218]
  exact h5n219_arithmetic

#print axioms h5n219_arithmetic
end StackSorting.RationalLift
