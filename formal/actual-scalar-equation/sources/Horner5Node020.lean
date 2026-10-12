import Horner5Base
import Horner5Node019
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p20 : BiPoly.Poly := [[(Int.ofNat 96), (Int.negSucc 191), (Int.negSucc 95)], [(Int.negSucc 95), (Int.ofNat 288)]]

theorem h5n20_arithmetic : BiPoly.add h5p7 h5p19=h5p20 := by
  decide +kernel

theorem h5n20 : h5e20.toBi mapPolyEnv=h5p20 := by
  change BiPoly.add (h5e7.toBi mapPolyEnv) (h5e19.toBi mapPolyEnv)=h5p20
  rw [h5n7, h5n19]
  exact h5n20_arithmetic

#print axioms h5n20_arithmetic
end StackSorting.RationalLift
