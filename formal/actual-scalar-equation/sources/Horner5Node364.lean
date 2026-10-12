import Horner5Base
import Horner5Node363
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p364 : BiPoly.Poly := [[(Int.negSucc 7), (Int.ofNat 16), (Int.ofNat 8)], [(Int.ofNat 8), (Int.negSucc 23)]]

theorem h5n364_arithmetic : BiPoly.add h5p355 h5p363=h5p364 := by
  decide +kernel

theorem h5n364 : h5e364.toBi mapPolyEnv=h5p364 := by
  change BiPoly.add (h5e355.toBi mapPolyEnv) (h5e363.toBi mapPolyEnv)=h5p364
  rw [h5n355, h5n363]
  exact h5n364_arithmetic

#print axioms h5n364_arithmetic
end StackSorting.RationalLift
