import Horner5Base
import Horner5Node310
namespace StackSorting.RationalLift
open StackSorting.CauchyRing StackSorting.ConcreteScalar
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

noncomputable def h5p311 : BiPoly.Poly := [[(Int.ofNat 48), (Int.negSucc 47)], [(Int.negSucc 47), (Int.ofNat 96)]]

theorem h5n311_arithmetic : BiPoly.add h5p191 h5p310=h5p311 := by
  decide +kernel

theorem h5n311 : h5e311.toBi mapPolyEnv=h5p311 := by
  change BiPoly.add (h5e191.toBi mapPolyEnv) (h5e310.toBi mapPolyEnv)=h5p311
  rw [h5n191, h5n310]
  exact h5n311_arithmetic

#print axioms h5n311_arithmetic
end StackSorting.RationalLift
